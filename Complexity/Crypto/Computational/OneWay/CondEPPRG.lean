/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.OneWay.Normalize
public import Complexity.Crypto.Computational.Pseudoentropy.WordReduction
public import Complexity.Probability.Entropy.BitString
public import Complexity.Crypto.Computational.GeneratorReindex
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Languages.Probabilistic.Notation
import Complexity.Crypto.Primitives.PRG.NextBit
import Complexity.Crypto.Game.Statistical
import Complexity.Probability.PMF.Uniform
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.Asymptotics
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime

/-!
# Conditional Entropy-Preserving Pseudorandom Generators from One-Way Functions

This module formalizes conditional entropy-preserving pseudorandom generators
($\mu$-condEP-PRGs) and their construction from one-way functions following
[Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020]. All section,
definition, theorem, lemma, and page locators follow the full version `arXiv:2009.11514v1`
(and ECCC TR20-052): Section 5 (Definition 5.1, §5.1, p. 11; Lemma 5.1, §5.3, p. 14; Lemma 5.2,
§5.3, p. 15; Theorem 5.5, §5.3, p. 15) and Appendix A (pp. 21–24). Note that in
`arXiv:2009.11514v1`, `Theorem` and `Definition` share one section counter while `Lemma` and
`Fact` share a separate section counter.

## Main definitions

* `Cslib.Crypto.CondEPPRG`: $(\mu, \gamma)$-conditional entropy-preserving pseudorandom generator
  with entropy-loss constant $\alpha$
  ([Liu and Pass, Definition 5.1, §5.1, p. 11 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Crypto.regularityBucket`: regularity buckets partitioning $\{0, 1\}^n$ by logarithmic
  preimage fiber size $\lfloor \log_2 |f^{-1}(f(x))| \rfloor \in \{0, \dots, n\}$
  ([Liu and Pass, Lemma 5.2, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).

## Main results

* `Cslib.Crypto.exists_regularity_bucket`: for every `f : BitString n → Image`, some regularity
  bucket $S_{n, r}$ has cardinality at least $2^n / (n + 1)$ and every $x \in S_{n, r}$ has fiber
  cardinality in $[2^r, 2^{r + 1})$
  ([Liu and Pass, Lemma 5.2 and Claim 3, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Crypto.OneWay.exists_condEPPRG`: every one-way function yields a
  $(1 / n^\delta, \gamma)$-condEP-PRG for any prescribed stretch factor $\gamma$ and polynomial
  security exponent $\delta$
  ([Liu and Pass, Theorem 5.5, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 5 and Appendix A).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Probability.PMF BitString Filter Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Definition 5.1: Conditional entropy-preserving PRG -/

/-- **[Liu and Pass, Definition 5.1, §5.1, p. 11 of arXiv:2009.11514v1][LiuPass2020]: Conditional
entropy-preserving pseudorandom generator ($\mu$-condEP-PRG).**
A deterministic polynomial-time function $G : \{0, 1\}^* \to \{0, 1\}^*$ is a
$(\mu, \gamma)$-condEP-PRG with entropy-loss constant $\alpha$ if:
1. $G$ is computable in polynomial time (`ComputableInPolyTime G encBits encBits`),
2. $G$ stretches every $n$-bit seed $z \in \{0, 1\}^n$ to length
   $n + \gamma \lfloor \log_2 n \rfloor$,
3. there exists a sequence of nonempty conditioning events $E_n \subseteq \{0, 1\}^n$ such that:
   - **(Conditional pseudorandomness):** For every strict PPT distinguisher $\mathcal{A}$,
     eventually in $n$, the distinguishing advantage between $G(U_n \mid E_n)$ and
     $U_{n + \gamma \lfloor \log_2 n \rfloor}$ is at most $\mu(n)$,
   - **(Conditional entropy preservation):** Eventually in $n$, the Shannon entropy of
     $G(U_n \mid E_n)$ is at least $n - \alpha \lfloor \log_2 n \rfloor$. -/
def CondEPPRG (G : List Bool → List Bool) (μ : ℕ → ℝ) (γ α : ℕ) : Prop :=
  ComputableInPolyTime G encBits encBits ∧
  (∀ z : List Bool, (G z).length = z.length + γ * Nat.log 2 z.length) ∧
  ∃ (E : ∀ n, Finset (BitString n)) (hE : ∀ n, (E n).Nonempty),
    (∀ adversary : Distinguisher, IsPPT encBool adversary →
      ∀ᶠ n : ℕ in atTop,
        (Game.advantage
          ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map G).bind
            fun y => ProbComp.eval (adversary n y))
          ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
            fun y => ProbComp.eval (adversary n y)) : ℝ) ≤ μ n) ∧
    (∀ᶠ n : ℕ in atTop,
      (n : ℝ) - (α : ℝ) * (Nat.log 2 n : ℝ) ≤
        PMF.entropy ((PMF.uniformOfFinset (E n) (hE n)).map fun x =>
          BitString.ofList (n + γ * Nat.log 2 n) (G (List.ofFn x))))

/-! ### Lemma 5.2: Regularity bucket pigeonhole -/

/-- Logarithmic fiber size
$\lfloor \log_2 |\{x' : f(x') = f(x)\}| \rfloor \in \mathrm{Fin}\; (n + 1)$
of an input $x \in \mathrm{BitString}\; n$ under $f$. -/
noncomputable def fiberLogIndex {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (x : BitString n) : Fin (n + 1) := by
  classical
  refine ⟨Nat.log 2 (Nat.card {x' : BitString n // f x' = f x}), ?_⟩
  have hcard : Nat.card {x' : BitString n // f x' = f x} ≤ 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using Fintype.card_subtype_le (fun x' : BitString n => f x' = f x)
  have hlog : Nat.log 2 (Nat.card {x' : BitString n // f x' = f x}) ≤ Nat.log 2 (2 ^ n) :=
    Nat.log_mono_right hcard
  rw [Nat.log_pow Nat.one_lt_two] at hlog
  omega

/-- The $r$-th regularity bucket $S_{n, r} = \{x \in \mathrm{BitString}\; n :
\lfloor \log_2 |f^{-1}(f(x))| \rfloor = r\}$
([Liu and Pass, Proof of Lemma 5.2, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]). -/
noncomputable def regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) : Finset (BitString n) := by
  classical
  exact Finset.univ.filter fun x => fiberLogIndex f x = r

@[simp]
theorem mem_regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) (x : BitString n) :
    x ∈ regularityBucket f r ↔ fiberLogIndex f x = r := by
  classical
  simp [regularityBucket]

/-- Every input $x$ in `regularityBucket f r` has fiber cardinality in $[2^r, 2^{r + 1})$. -/
theorem card_fiber_of_mem_regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) {x : BitString n} (hx : x ∈ regularityBucket f r) :
    2 ^ r.val ≤ Nat.card {x' : BitString n // f x' = f x} ∧
      Nat.card {x' : BitString n // f x' = f x} < 2 ^ (r.val + 1) := by
  classical
  have hfib : (fiberLogIndex f x).val = r.val :=
    congrArg Fin.val ((mem_regularityBucket f r x).mp hx)
  dsimp [fiberLogIndex] at hfib
  have hne : Nat.card {x' : BitString n // f x' = f x} ≠ 0 := by
    have : Nonempty {x' : BitString n // f x' = f x} := ⟨⟨x, rfl⟩⟩
    exact Nat.card_pos.ne'
  rw [← hfib]
  exact ⟨Nat.pow_log_le_self 2 hne, Nat.lt_pow_succ_log_self Nat.one_lt_two _⟩

/-- `regularityBucket f r` is a union of full fibers of `f`: if $f(x') = f(x)$, then
$x' \in S_{n, r} \iff x \in S_{n, r}$. -/
theorem mem_regularityBucket_of_eq {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) {x x' : BitString n} (heq : f x' = f x) :
    x' ∈ regularityBucket f r ↔ x ∈ regularityBucket f r := by
  rw [mem_regularityBucket, mem_regularityBucket]
  have hidx : fiberLogIndex f x' = fiberLogIndex f x := by
    ext
    dsimp [fiberLogIndex]
    congr 1
    simp [heq]
  rw [hidx]

/-- **[Liu and Pass, Lemma 5.2 and Claim 3, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]:
Existence of a dense regularity bucket.**
For every $n$ and every function $f : \mathrm{BitString}\; n \to \mathrm{Image}$, there exists a
regularity index $r \in \mathrm{Fin}\; (n + 1)$ such that the bucket $S_{n, r}$ has cardinality at
least $2^n / (n + 1)$ (i.e. $2^n \le (n + 1) \cdot |S_{n, r}|$), is nonempty, and every
$x \in S_{n, r}$ has fiber size in $[2^r, 2^{r + 1})$. -/
theorem exists_regularity_bucket {n : ℕ} {Image : Type*} (f : BitString n → Image) :
    ∃ r : Fin (n + 1),
      (regularityBucket f r).Nonempty ∧
      2 ^ n ≤ (n + 1) * (regularityBucket f r).card ∧
      ∀ x ∈ regularityBucket f r,
        2 ^ r.val ≤ Nat.card {x' : BitString n // f x' = f x} ∧
          Nat.card {x' : BitString n // f x' = f x} < 2 ^ (r.val + 1) := by
  classical
  have hsum : ∑ r : Fin (n + 1), (regularityBucket f r).card = 2 ^ n := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fiberLogIndex f) (s := (Finset.univ : Finset (BitString n)))
      (t := (Finset.univ : Finset (Fin (n + 1)))) (fun x _ => Finset.mem_univ _)
    simpa [regularityBucket] using h.symm
  obtain ⟨r, -, hr⟩ : ∃ r ∈ (Finset.univ : Finset (Fin (n + 1))),
      2 ^ n ≤ (n + 1) * (regularityBucket f r).card := by
    by_contra! hlt
    have hsum_lt : ∑ r : Fin (n + 1), ((n + 1) * (regularityBucket f r).card) <
        ∑ _r : Fin (n + 1), 2 ^ n := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ fun r hr => hlt r hr
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum_lt
    exact (lt_irrefl _ hsum_lt).elim
  have hne : (regularityBucket f r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.card_empty, mul_zero] at hr
    have : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
    omega
  exact ⟨r, hne, hr, fun x hx => card_fiber_of_mem_regularityBucket f r hx⟩

/-! ### Fiber resampling and regularity bucket mass bounds -/

private theorem uniformOfFintype_fiber_map_val_apply {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (x₀ z : BitString n) :
    haveI : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    ((PMF.uniformOfFintype {x : BitString n // f x = f x₀}).map Subtype.val) z =
      if f z = f x₀ then (Fintype.card {x : BitString n // f x = f z} : ℝ≥0∞)⁻¹ else 0 := by
  have : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  rw [PMF.map_apply, tsum_fintype]
  split_ifs with hfz
  · have hmem : (⟨z, hfz⟩ : {x : BitString n // f x = f x₀}) ∈ Finset.univ := Finset.mem_univ _
    rw [Finset.sum_eq_single ⟨z, hfz⟩]
    · simp only [↓reduceIte, PMF.uniformOfFintype_apply]
      congr 2
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [hfz])
    · intro b _ hb
      have hne : z ≠ b.1 := fun h => hb (Subtype.ext h.symm)
      simp [hne]
    · intro habs; exact (habs hmem).elim
  · refine Finset.sum_eq_zero fun b _ => ?_
    have hne : z ≠ b.1 := fun h => hfz (h ▸ b.2)
    simp [hne]

/-- Resampling a preimage uniformly from the fiber of an element drawn uniformly from a
nonempty regularity bucket recovers `uniformOfFinset (regularityBucket f r) hS`. -/
theorem bind_regularityBucket_fiber_eq {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty) :
    haveI (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    (PMF.uniformOfFinset (regularityBucket f r) hS).bind
      (fun x₀ => (PMF.uniformOfFintype {x : BitString n // f x = f x₀}).map Subtype.val) =
      PMF.uniformOfFinset (regularityBucket f r) hS := by
  classical
  have (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  ext z
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [uniformOfFintype_fiber_map_val_apply, PMF.uniformOfFinset_apply]
  by_cases hz : z ∈ regularityBucket f r
  · simp only [hz, ↓reduceIte]
    have : Nonempty {x : BitString n // f x = f z} := ⟨⟨z, rfl⟩⟩
    have hcard_eq : (Finset.univ.filter fun x₀ : BitString n => f x₀ = f z).card =
        Fintype.card {x : BitString n // f x = f z} :=
      (Fintype.card_subtype _).symm
    conv_rhs =>
      rw [← mul_one ((regularityBucket f r).card : ℝ≥0∞)⁻¹,
        ← ENNReal.mul_inv_cancel (a := (Fintype.card {x : BitString n // f x = f z} : ℝ≥0∞))
          (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
        ← mul_assoc, mul_comm ((regularityBucket f r).card : ℝ≥0∞)⁻¹, mul_assoc,
        ← hcard_eq, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x₀ _ => ?_
    by_cases hfx : f x₀ = f z
    · have hx₀ : x₀ ∈ regularityBucket f r :=
        (mem_regularityBucket_of_eq f r hfx).mpr hz
      simp only [hx₀, hfx, hcard_eq, ↓reduceIte]
    · have hfx' : ¬ (f z = f x₀) := Ne.symm hfx
      simp only [hfx, hfx', ↓reduceIte, mul_zero]
  · simp only [hz, ↓reduceIte]
    refine Finset.sum_eq_zero fun x₀ _ => ?_
    by_cases hx₀ : x₀ ∈ regularityBucket f r
    · have hfx : f z ≠ f x₀ := fun h => hz ((mem_regularityBucket_of_eq f r h).mpr hx₀)
      simp [hx₀, hfx]
    · simp [hx₀]

/-- Averaging any real-valued function over `x₀ ← uniformOfFinset (regularityBucket f r)` and
`x ← uniformOfFintype {x // f x = f x₀}` equals its average over `x ← uniformOfFinset`. -/
theorem sum_regularityBucket_fiber_eq {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty)
    (Φ : BitString n → ℝ) :
    haveI (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    ∑ x₀ : BitString n, (PMF.uniformOfFinset (regularityBucket f r) hS x₀).toReal *
      ∑ x : {x : BitString n // f x = f x₀},
        (PMF.uniformOfFintype {x : BitString n // f x = f x₀} x).toReal * Φ x.1 =
      ∑ x : BitString n, (PMF.uniformOfFinset (regularityBucket f r) hS x).toReal * Φ x := by
  have (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  conv_lhs =>
    arg 2; ext x₀
    rw [← sum_map_mul (PMF.uniformOfFintype {x : BitString n // f x = f x₀}) Subtype.val Φ]
  rw [← sum_bind_mul, bind_regularityBucket_fiber_eq]

/-- Pointwise image probability bound when $x$ is drawn uniformly from a dense regularity bucket
$S_{n, r}$ with $2^n \le (n + 1) \cdot |S_{n, r}|$. -/
theorem mass_map_regularityBucket_le {n : ℕ} {Image : Type*}
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ n ≤ (n + 1) * (regularityBucket f r).card) (y : Image) :
    (((PMF.uniformOfFinset (regularityBucket f r) hS).map f) y).toReal ≤
      (2 * (n + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ n := by
  classical
  let S := regularityBucket f r
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hmap : ((PMF.uniformOfFinset S hS).map f) y =
      ((S.filter fun x => f x = y).card : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ := by
    rw [PMF.map_apply, tsum_fintype]
    conv_rhs =>
      rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.filter_univ_mem (s := S),
        Finset.filter_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [PMF.uniformOfFinset_apply]
    split_ifs <;> simp_all
  rw [hmap, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← div_eq_mul_inv]
  have hcard_le : ((S.filter fun x => f x = y).card : ℝ) ≤ 2 * (2 : ℝ) ^ r.val := by
    rcases (S.filter fun x => f x = y).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
    · rw [hemp, Finset.card_empty, Nat.cast_zero]
      positivity
    · rw [Finset.mem_filter] at hx₀
      have hsub : S.filter (fun x => f x = y) ⊆ Finset.univ.filter (fun x => f x = f x₀) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, hx.2.trans hx₀.2.symm⟩
      have hle1 : (S.filter fun x => f x = y).card ≤
          (Finset.univ.filter fun x => f x = f x₀).card := Finset.card_le_card hsub
      have hle2 : (Finset.univ.filter fun x => f x = f x₀).card =
          Nat.card {x : BitString n // f x = f x₀} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hlt := (card_fiber_of_mem_regularityBucket f r hx₀.1).2
      have hle_nat : (S.filter fun x => f x = y).card ≤ 2 * 2 ^ r.val := by
        rw [pow_succ'] at hlt
        omega
      exact_mod_cast hle_nat
  have hdense_real : (2 : ℝ) ^ n ≤ (n + 1 : ℝ) * (S.card : ℝ) := by exact_mod_cast hdense
  rw [div_le_div_iff₀ hS_pos (by positivity)]
  calc
    ((S.filter fun x => f x = y).card : ℝ) * (2 : ℝ) ^ n
      ≤ (2 * (2 : ℝ) ^ r.val) * ((n + 1 : ℝ) * (S.card : ℝ)) :=
      mul_le_mul hcard_le hdense_real (by positivity) (by positivity)
    _ = 2 * (n + 1 : ℝ) * (2 : ℝ) ^ r.val * (S.card : ℝ) := by ring

/-- For any nonnegative function $G : \mathrm{BitString}\; n \to \mathbb{R}$, its expectation over
$S_{n, r}$ (with $2^n \le (n + 1) |S_{n, r}|$) is at most $(n + 1)$ times its expectation over the
uniform distribution on $\mathrm{BitString}\; n$. -/
private theorem sum_uniformOfFinset_le_mul_uniformOfFintype {n : ℕ}
    (S : Finset (BitString n)) (hS : S.Nonempty) (hdense : 2 ^ n ≤ (n + 1) * S.card)
    (G : BitString n → ℝ) (hG : ∀ x, 0 ≤ G x) :
    ∑ x : BitString n, (PMF.uniformOfFinset S hS x).toReal * G x ≤
      (n + 1 : ℝ) * ∑ x : BitString n, (PMF.uniformOfFintype (BitString n) x).toReal * G x := by
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hdense_real : (2 : ℝ) ^ n ≤ (n + 1 : ℝ) * (S.card : ℝ) := by exact_mod_cast hdense
  have hinv_le : ((S.card : ℝ))⁻¹ ≤ (n + 1 : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hS_pos (by positivity)]
    linarith
  refine Finset.sum_le_sum ?_ |> le_trans <| by rw [Finset.mul_sum]
  intro x _
  rw [PMF.uniformOfFinset_apply, PMF.uniformOfFintype_apply]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with hx
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
    calc
      (S.card : ℝ)⁻¹ * G x ≤ ((n + 1 : ℝ) * ((2 : ℝ) ^ n)⁻¹) * G x :=
        mul_le_mul_of_nonneg_right hinv_le (hG x)
      _ = (n + 1 : ℝ) * (((2 : ℝ) ^ n)⁻¹ * G x) := by ring
  · rw [ENNReal.toReal_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg ENNReal.toReal_nonneg (hG x))

/-! ### Trivial inverter and regularity deficit bound -/

/-- The trivial inverter that ignores the challenge image and samples a uniform $k$-bit string. -/
private noncomputable def trivialInverter : Inverter := fun k _ => BitString.sampleList k

@[local program_certificate]
private theorem isPPT_trivialInverter : IsPPT encBits trivialInverter := by
  unfold trivialInverter
  ppt

/-- If $S_{k, r}$ is a regularity bucket of `finiteFunction` with
$2^k \le (k + 1) \cdot |S_{k, r}|$, then the trivial inverter inverts $g$ at parameter $k$
with probability at least $\frac{2^r}{(k + 1) \cdot 2^k}$. -/
private theorem trivialInverter_succ_ge {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (himgLen : ∀ x, (g x).length = imgLen x.length) (k : ℕ)
    (r : Fin (k + 1))
    (hdense : 2 ^ k ≤ (k + 1) *
      (regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) r).card) :
    ((2 : ℝ) ^ r.val) / ((k + 1 : ℝ) * (2 : ℝ) ^ k) ≤
      (Game.succProbability (ProbComp.eval (inversionGame g trivialInverter k)) : ℝ) := by
  classical
  let f : BitString k → BitString (imgLen k) := fun x => ofList (imgLen k) (g (List.ofFn x))
  let S := regularityBucket f r
  have hfeq : ∀ x x' : BitString k,
      (g (List.ofFn x') == g (List.ofFn x)) = decide (f x' = f x) := by
    intro x x'
    rw [beq_eq_decide]
    apply decide_eq_decide.mpr
    constructor
    · intro h; simp [f, h]
    · intro h
      have h1 := congrArg List.ofFn h
      rwa [ofFn_ofList (by simp [himgLen]), ofFn_ofList (by simp [himgLen])] at h1
  have heval : (Game.succProbability (ProbComp.eval (inversionGame g trivialInverter k)) : ℝ) =
      ∑ x : BitString k, (PMF.uniformOfFintype (BitString k) x).toReal *
        ∑ x' : BitString k, (PMF.uniformOfFintype (BitString k) x').toReal *
          (if f x' = f x then 1 else 0) := by
    rw [Game.coe_succProbability]
    simp only [inversionGame, trivialInverter, ProbComp.eval_bind, BitString.eval_sampleList,
      ProbComp.eval_pure, BitString.uniformList, PMF.bind_map, Function.comp_def,
      bind_apply_toReal, PMF.pure_apply, hfeq]
    refine Finset.sum_congr rfl fun x _ => congrArg _ (Finset.sum_congr rfl fun x' _ => ?_)
    by_cases h : f x' = f x <;> simp [h]
  rw [heval]
  have hpoint : ∀ x : BitString k,
      (if x ∈ S then ((2 : ℝ) ^ r.val) / (2 : ℝ) ^ k else 0) ≤
        ∑ x' : BitString k, (PMF.uniformOfFintype (BitString k) x').toReal *
          (if f x' = f x then 1 else 0) := by
    intro x
    have hinner : (∑ x' : BitString k, (PMF.uniformOfFintype (BitString k) x').toReal *
        (if f x' = f x then 1 else 0)) =
        (Nat.card {x' : BitString k // f x' = f x} : ℝ) / (2 : ℝ) ^ k := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum, Finset.sum_boole,
        Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_inv_mul]
    rw [hinner]
    split_ifs with hx
    · refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact_mod_cast (card_fiber_of_mem_regularityBucket f r hx).1
    · positivity
  have hsum_le : (∑ x : BitString k, (PMF.uniformOfFintype (BitString k) x).toReal *
      (if x ∈ S then ((2 : ℝ) ^ r.val) / (2 : ℝ) ^ k else 0)) ≤
      ∑ x : BitString k, (PMF.uniformOfFintype (BitString k) x).toReal *
        ∑ x' : BitString k, (PMF.uniformOfFintype (BitString k) x').toReal *
          (if f x' = f x then 1 else 0) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) ENNReal.toReal_nonneg
  refine le_trans ?_ hsum_le
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum, ← Finset.sum_filter,
    Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
  have hdense_real : (2 : ℝ) ^ k ≤ (k + 1 : ℝ) * (S.card : ℝ) := by exact_mod_cast hdense
  rw [div_le_iff₀ (by positivity)]
  have hrew : ((2 : ℝ) ^ k)⁻¹ * ((S.card : ℝ) * ((2 : ℝ) ^ r.val / (2 : ℝ) ^ k)) *
      ((k + 1 : ℝ) * (2 : ℝ) ^ k) =
      ((2 : ℝ) ^ r.val / (2 : ℝ) ^ k) * ((k + 1 : ℝ) * (S.card : ℝ)) := by
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  rw [hrew]
  have hgoal := mul_le_mul_of_nonneg_left hdense_real
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r.val / (2 : ℝ) ^ k)
  have hcancel : ((2 : ℝ) ^ r.val / (2 : ℝ) ^ k) * (2 : ℝ) ^ k = (2 : ℝ) ^ r.val :=
    div_mul_cancel₀ _ (by positivity)
  linarith

/-- For any one-way function $g$ with fixed output length `imgLen` and any sequence of dense
regularity indices $r(k)$, for every constant $D \in \mathbb{N}$ we eventually have
$r(k) + D \lfloor \log_2 k \rfloor \le k$. -/
theorem eventually_regularity_gap {g : List Bool → List Bool} (hg : OneWay g)
    {imgLen : ℕ → ℕ} (himgLen : ∀ x, (g x).length = imgLen x.length)
    (r : ∀ k, Fin (k + 1))
    (hdense : ∀ k, 2 ^ k ≤ (k + 1) *
      (regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k)).card)
    (D : ℕ) :
    ∀ᶠ k : ℕ in atTop, (r k).val + D * Nat.log 2 k ≤ k := by
  have hneg :=
    (hg.inversion_negligible trivialInverter isPPT_trivialInverter).eventually_le_inv_polynomial
      (p := fun k => (k + 1) ^ (D + 1)) (by fun_prop) (fun k => by positivity)
  filter_upwards [hneg, eventually_ge_atTop 2] with k hk hk2
  have hsucc := trivialInverter_succ_ge himgLen k (r k) (hdense k)
  have hk_real : (Game.succProbability (ProbComp.eval (inversionGame g trivialInverter k)) : ℝ) ≤
      1 / ((k + 1 : ℝ) ^ (D + 1)) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hk
  have hcomb : ((2 : ℝ) ^ (r k).val) / ((k + 1 : ℝ) * (2 : ℝ) ^ k) ≤
      1 / ((k + 1 : ℝ) ^ (D + 1)) :=
    hsucc.trans hk_real
  have hk_log : (2 : ℝ) ^ (Nat.log 2 k) ≤ (k : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_D : ((2 : ℝ) ^ (Nat.log 2 k)) ^ D ≤ (k + 1 : ℝ) ^ D :=
    pow_le_pow_left₀ (by positivity) (by linarith) D
  have hcross : (2 : ℝ) ^ (r k).val * (k + 1 : ℝ) ^ (D + 1) ≤ (k + 1 : ℝ) * (2 : ℝ) ^ k := by
    rwa [div_le_div_iff₀ (by positivity) (by positivity), one_mul] at hcomb
  have hpow_D : (k + 1 : ℝ) ^ (D + 1) = (k + 1 : ℝ) * (k + 1 : ℝ) ^ D := pow_succ' (k + 1 : ℝ) D
  have hpow_le : (2 : ℝ) ^ ((r k).val + D * Nat.log 2 k) ≤ (2 : ℝ) ^ k := by
    have hpos : (0 : ℝ) < k + 1 := by positivity
    have h1 : (2 : ℝ) ^ (r k).val * (k + 1 : ℝ) ^ D ≤ (2 : ℝ) ^ k := by
      rw [hpow_D] at hcross
      nlinarith
    calc
      (2 : ℝ) ^ ((r k).val + D * Nat.log 2 k)
        = (2 : ℝ) ^ (r k).val * ((2 : ℝ) ^ (Nat.log 2 k)) ^ D := by
          rw [pow_add, pow_mul']
      _ ≤ (2 : ℝ) ^ (r k).val * (k + 1 : ℝ) ^ D :=
          mul_le_mul_of_nonneg_left hlog_D (by positivity)
      _ ≤ (2 : ℝ) ^ k := h1
  have hpow_nat : 2 ^ ((r k).val + D * Nat.log 2 k) ≤ 2 ^ k := by
    exact_mod_cast hpow_le
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow_nat

/-! ### Generator parameters and deterministic construction -/

/-- Binary encoding width $\lfloor \log_2 k \rfloor + 1$ for a regularity index
$r \in \{0, \dots, k\}$. -/
private def regWidth (k : ℕ) : ℕ := Nat.log 2 k + 1

/-- Every $r \le k$ fits in `regWidth k` binary bits: $r < 2^{\mathrm{regWidth}\; k}$. -/
private theorem lt_two_pow_regWidth {k r : ℕ} (hr : r ≤ k) : r < 2 ^ regWidth k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [regWidth]; omega
  ·exact lt_of_le_of_lt hr (Nat.lt_pow_succ_log_self Nat.one_lt_two k)

/-- Maximum Goldreich–Levin output count allocated in the matrix $h_2$ at core parameter $k$. -/
private def mMax (d γ_core k : ℕ) : ℕ :=
  2 * (d * Nat.log 2 k) + γ_core * Nat.log 2 k + Nat.log 2 k + 1

/-- Total number of rows in the second universal hash matrix $h_2$ at core parameter $k$. -/
private def h2Rows (d γ_core k : ℕ) : ℕ := k + mMax d γ_core k

/-- Core seed length at OWF input length $k$:
$\mathrm{regWidth}(k) + k + k \cdot \mathrm{imgLen}(k) +
\mathrm{h2Rows}(d, \gamma_{\text{core}}, k) \cdot k$. -/
private def coreSeedLen (imgLen : ℕ → ℕ) (d γ_core k : ℕ) : ℕ :=
  regWidth k + k + k * imgLen k + h2Rows d γ_core k * k

/-- Actual Goldreich–Levin bit count extracted at core parameter $k$ and total seed length $n$. -/
private def mActual (d γ k n : ℕ) : ℕ :=
  2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 + γ * Nat.log 2 n

/-- Number of LHL bits extracted from $x$ by $h_2$ for regularity index $r$. -/
private def l2Val (d k r : ℕ) : ℕ := min (r - d * Nat.log 2 k) (k - 2 * (d * Nat.log 2 k))

/-- Number of LHL bits extracted from $g(x)$ by $h_1$ for regularity index $r$. -/
private def l1Val (d k r : ℕ) : ℕ := (k - 2 * (d * Nat.log 2 k)) - l2Val d k r

/-- Length of the LHL prefix of the generator output before the `mActual` Goldreich–Levin bits. -/
private def lhlPrefixLen (d k n : ℕ) : ℕ := n - (2 * (d * Nat.log 2 k) + Nat.log 2 k + 1)

private theorem l1Val_add_l2Val (d k r : ℕ) :
    l1Val d k r + l2Val d k r = k - 2 * (d * Nat.log 2 k) := by
  unfold l1Val l2Val
  omega

private theorem l1Val_le (d k r : ℕ) : l1Val d k r ≤ k := by
  unfold l1Val
  omega

private theorem l2Val_le (d k r : ℕ) : l2Val d k r ≤ k := by
  unfold l2Val
  omega

private theorem l2Val_eq_of_gap {d k r : ℕ} (hgap : r + d * Nat.log 2 k ≤ k) :
    l2Val d k r = r - d * Nat.log 2 k := by
  unfold l2Val
  omega

private theorem l1Val_add_le_of_gap {d k r : ℕ} (hgap : r + d * Nat.log 2 k ≤ k) :
    l1Val d k r + d * Nat.log 2 k ≤ k - r := by
  have hsum := l1Val_add_l2Val d k r
  have hl2 := l2Val_eq_of_gap hgap
  omega

private theorem mActual_le_mMax {d γ γ_core k n : ℕ}
    (hlog : γ * Nat.log 2 n ≤ γ_core * Nat.log 2 k) :
    mActual d γ k n ≤ mMax d γ_core k := by
  unfold mActual mMax
  omega

private theorem lhlPrefixLen_add_mActual {d γ k n : ℕ}
    (hle : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n) :
    lhlPrefixLen d k n + mActual d γ k n = n + γ * Nat.log 2 n := by
  unfold lhlPrefixLen mActual
  omega

private theorem coreSeedLen_ge_succ (imgLen : ℕ → ℕ) (d γ_core k : ℕ) :
    k + 1 ≤ coreSeedLen imgLen d γ_core k := by
  unfold coreSeedLen regWidth
  omega

@[local fun_prop]
private theorem computableTidilyInPolyTime_regWidth {α : Type} {encode : α ↪ List Bool}
    {k : α → ℕ} (hk : ComputableTidilyInPolyTime k encode encUnary) :
    ComputableTidilyInPolyTime (fun a => regWidth (k a)) encode encUnary := by
  unfold regWidth
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_mMax {α : Type} {encode : α ↪ List Bool}
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableTidilyInPolyTime k encode encUnary) :
    ComputableTidilyInPolyTime (fun a => mMax d γ_core (k a)) encode encUnary := by
  unfold mMax
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_h2Rows {α : Type} {encode : α ↪ List Bool}
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableTidilyInPolyTime k encode encUnary) :
    ComputableTidilyInPolyTime (fun a => h2Rows d γ_core (k a)) encode encUnary := by
  unfold h2Rows
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_coreSeedLen {α : Type} {encode : α ↪ List Bool}
    {imgLen : ℕ → ℕ} (himgLen : ComputableTidilyInPolyTime imgLen encUnary encUnary)
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableTidilyInPolyTime k encode encUnary) :
    ComputableTidilyInPolyTime (fun a => coreSeedLen imgLen d γ_core (k a)) encode encUnary := by
  unfold coreSeedLen
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_mActual {α : Type} {encode : α ↪ List Bool}
    (d γ : ℕ) {k n : α → ℕ}
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hn : ComputableTidilyInPolyTime n encode encUnary) :
    ComputableTidilyInPolyTime (fun a => mActual d γ (k a) (n a)) encode encUnary := by
  unfold mActual
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_l2Val {α : Type} {encode : α ↪ List Bool}
    (d : ℕ) {k r : α → ℕ}
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hr : ComputableTidilyInPolyTime r encode encUnary) :
    ComputableTidilyInPolyTime (fun a => l2Val d (k a) (r a)) encode encUnary := by
  unfold l2Val
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_l1Val {α : Type} {encode : α ↪ List Bool}
    (d : ℕ) {k r : α → ℕ}
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hr : ComputableTidilyInPolyTime r encode encUnary) :
    ComputableTidilyInPolyTime (fun a => l1Val d (k a) (r a)) encode encUnary := by
  unfold l1Val
  fun_prop

/-- Unpadded output of the conditional entropy-preserving generator on seed `z`:
`pad ++ h1 ++ LinearHash.wordHash l1 h1 (g x) ++ h2 ++ LinearHash.wordHash (l2 + mActual) h2 x`. -/
private def rawGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) : List Bool :=
  let n := z.length
  let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  let w := regWidth k
  let r := boundedBinaryValue k (z.take w)
  let l1 := l1Val d k r
  let l2 := l2Val d k r
  let x := (z.drop w).take k
  let h1 := (z.drop (w + k)).take (k * imgLen k)
  let h2 := (z.drop (w + k + k * imgLen k)).take (h2Rows d γ_core k * k)
  let pad := z.drop (coreSeedLen imgLen d γ_core k)
  pad ++ h1 ++ LinearHash.wordHash l1 h1 (g x) ++
    h2 ++ LinearHash.wordHash (l2 + mActual d γ k n) h2 x

/-- Full deterministic conditional entropy-preserving generator `G` ([Liu and Pass, Proof of
Theorem 5.5, §5.3, p. 15 and Appendix A, pp. 21–24 of arXiv:2009.11514v1][LiuPass2020]),
normalized to output length `z.length + γ * Nat.log 2 z.length` on every input `z`. -/
private def fullGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) : List Bool :=
  let targetLen := z.length + γ * Nat.log 2 z.length
  (rawGen g imgLen d γ_core γ z ++ List.replicate targetLen false).take targetLen

@[simp]
private theorem length_fullGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) :
    (fullGen g imgLen d γ_core γ z).length = z.length + γ * Nat.log 2 z.length := by
  simp [fullGen]

/-- When `coreSeedLen k ≤ z.length` and `2 * (d * Nat.log 2 k) ≤ k`, `rawGen` already has length
`z.length + γ * Nat.log 2 z.length`, so `fullGen` equals `rawGen`. -/
private theorem fullGen_eq_rawGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ} {d γ_core γ : ℕ}
    {z : List Bool}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length) ≤ z.length)
    (hk : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length) :
    fullGen g imgLen d γ_core γ z = rawGen g imgLen d γ_core γ z := by
  have hraw_len : (rawGen g imgLen d γ_core γ z).length = z.length + γ * Nat.log 2 z.length := by
    unfold rawGen
    dsimp only
    set n := z.length
    set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    set w := regWidth k
    set r := boundedBinaryValue k (z.take w)
    have hl12 : l1Val d k r + l2Val d k r = k - 2 * (d * Nat.log 2 k) := l1Val_add_l2Val d k r
    have hcore : w + k + k * imgLen k + h2Rows d γ_core k * k ≤ n := hfits
    have hw : w = Nat.log 2 k + 1 := rfl
    have hm : mActual d γ k n = 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 + γ * Nat.log 2 n := rfl
    have hcs : coreSeedLen imgLen d γ_core k = w + k + k * imgLen k + h2Rows d γ_core k * k := rfl
    simp only [hcs, List.length_append, List.length_drop, List.length_take,
      LinearHash.length_wordHash]
    omega
  rw [fullGen, List.take_left' hraw_len]

@[local fun_prop]
private theorem computableTidilyInPolyTime_rawGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (hg : ComputableTidilyInPolyTime g encBits encBits)
    (himgLen : ComputableTidilyInPolyTime imgLen encUnary encUnary)
    (d γ_core γ : ℕ) :
    ComputableTidilyInPolyTime (rawGen g imgLen d γ_core γ) encBits encBits := by
  let kFn (z : List Bool) := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length
  let wFn (z : List Bool) := regWidth (kFn z)
  let rFn (z : List Bool) := boundedBinaryValue (kFn z) (z.take (wFn z))
  let xFn (z : List Bool) := (z.drop (wFn z)).take (kFn z)
  let h1Fn (z : List Bool) := (z.drop (wFn z + kFn z)).take (kFn z * imgLen (kFn z))
  let h2Fn (z : List Bool) :=
    (z.drop (wFn z + kFn z + kFn z * imgLen (kFn z))).take (h2Rows d γ_core (kFn z) * kFn z)
  let padFn (z : List Bool) := z.drop (coreSeedLen imgLen d γ_core (kFn z))
  have hk : ComputableTidilyInPolyTime kFn encBits encUnary :=
    (GeneratorReindex.isPolyTime_parameter (by fun_prop) (by fun_prop)).tidy
  have hw : ComputableTidilyInPolyTime wFn encBits encUnary := by unfold wFn; fun_prop
  have hr : ComputableTidilyInPolyTime rFn encBits encUnary := by unfold rFn; fun_prop
  have hx : ComputableTidilyInPolyTime xFn encBits encBits := by unfold xFn; fun_prop
  have hh1 : ComputableTidilyInPolyTime h1Fn encBits encBits := by unfold h1Fn; fun_prop
  have hh2 : ComputableTidilyInPolyTime h2Fn encBits encBits := by unfold h2Fn; fun_prop
  have hpad : ComputableTidilyInPolyTime padFn encBits encBits := by unfold padFn; fun_prop
  have hd1 : ComputableTidilyInPolyTime
      (fun z => LinearHash.wordHash (l1Val d (kFn z) (rFn z)) (h1Fn z) (g (xFn z)))
      encBits encBits := by fun_prop
  have hd2 : ComputableTidilyInPolyTime
      (fun z => LinearHash.wordHash
        (l2Val d (kFn z) (rFn z) + mActual d γ (kFn z) z.length) (h2Fn z) (xFn z))
      encBits encBits := by fun_prop
  change ComputableTidilyInPolyTime
    (fun z => padFn z ++ h1Fn z ++
      LinearHash.wordHash (l1Val d (kFn z) (rFn z)) (h1Fn z) (g (xFn z)) ++
      h2Fn z ++
      LinearHash.wordHash
        (l2Val d (kFn z) (rFn z) + mActual d γ (kFn z) z.length) (h2Fn z) (xFn z))
    encBits encBits
  fun_prop

private theorem computableInPolyTime_fullGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (hg : ComputableTidilyInPolyTime g encBits encBits)
    (himgLen : ComputableTidilyInPolyTime imgLen encUnary encUnary)
    (d γ_core γ : ℕ) :
    ComputableInPolyTime (fullGen g imgLen d γ_core γ) encBits encBits := by
  unfold fullGen
  fun_prop

/-! ### Seed packing and conditioning events $E_n$ -/

/-- Mapping a nonempty finset along an embedding commutes with `PMF.uniformOfFinset`. -/
private theorem uniformOfFinset_map {α β : Type*} [Finite α]
    (s : Finset α) (hs : s.Nonempty) (e : α ↪ β) :
    PMF.uniformOfFinset (s.map e) (Finset.map_nonempty.mpr hs) =
      (PMF.uniformOfFinset s hs).map e := by
  classical
  let := Fintype.ofFinite α
  ext b
  rw [PMF.uniformOfFinset_apply, PMF.map_apply, tsum_fintype, Finset.card_map]
  by_cases hb : b ∈ s.map e
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    rw [ite_eq_left (Finset.mem_map_of_mem e ha), Finset.sum_eq_single a]
    · simp [PMF.uniformOfFinset_apply, ha]
    · intro a' _ ha'
      have hne : e a ≠ e a' := fun h => ha' (e.injective h).symm
      simp [hne]
    · intro habs; exact (habs (Finset.mem_univ a)).elim
  · rw [ite_eq_right hb]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    by_cases ha : a ∈ s
    · have hne : b ≠ e a := fun h => hb (h ▸ Finset.mem_map_of_mem e ha)
      simp [hne]
    · simp [PMF.uniformOfFinset_apply, ha]

/-- Product of a nonempty finset with `Finset.univ` under `PMF.uniformOfFinset` factors into
independent sampling from `PMF.uniformOfFinset` and `PMF.uniformOfFintype`. -/
private theorem uniformOfFinset_product_univ {α β : Type*} [Finite α] [Fintype β] [Nonempty β]
    (s : Finset α) (hs : s.Nonempty) :
    PMF.uniformOfFinset (s ×ˢ (Finset.univ : Finset β)) (hs.product Finset.univ_nonempty) =
      (PMF.uniformOfFinset s hs).bind fun a =>
        (PMF.uniformOfFintype β).map fun b => (a, b) := by
  classical
  let := Fintype.ofFinite α
  ext ⟨a, b⟩
  rw [PMF.uniformOfFinset_apply, PMF.bind_apply, tsum_fintype, Finset.card_product,
    Finset.card_univ]
  simp only [Finset.mem_product, Finset.mem_univ, and_true, PMF.uniformOfFinset_apply,
    PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp only [true_and]
    rw [Finset.sum_eq_single b]
    · by_cases ha : a ∈ s
      · simp [ha, Nat.cast_mul, ENNReal.mul_inv]
      · simp [ha]
    · intro b' _ hb'; simp [hb'.symm]
    · intro habs; exact (habs (Finset.mem_univ b)).elim
  · intro a' _ ha'
    have hne : ¬ (a = a') := Ne.symm ha'
    simp [hne]
  · intro habs; exact (habs (Finset.mem_univ a)).elim

/-- Uniform components `(h1, h2, pad)` of a seed at core parameter `k` and seed length `n`. -/
private abbrev RestTuple (imgLen : ℕ → ℕ) (d γ_core k n : ℕ) : Type :=
  BitString (k * imgLen k) × BitString (h2Rows d γ_core k * k) ×
    BitString (n - coreSeedLen imgLen d γ_core k)

/-- Structured seed tuple `(x, h1, h2, pad)` at core parameter `k` and seed length `n`. -/
private abbrev SeedTuple (imgLen : ℕ → ℕ) (d γ_core k n : ℕ) : Type :=
  BitString k × RestTuple imgLen d γ_core k n

/-- Concatenate the regularity header `binaryWord (regWidth k) r` with `x, h1, h2, pad`. -/
private def packSeedWords {imgLen : ℕ → ℕ} {d γ_core k n : ℕ} (r : ℕ)
    (t : SeedTuple imgLen d γ_core k n) : List Bool :=
  binaryWord (regWidth k) r ++ List.ofFn t.1 ++ List.ofFn t.2.1 ++
    List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2

private theorem length_packSeedWords {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (t : SeedTuple imgLen d γ_core k n) :
    (packSeedWords r t).length = n := by
  have hrw : (binaryWord (regWidth k) r).length = regWidth k :=
    length_binaryWord (lt_two_pow_regWidth hr)
  have hcs : coreSeedLen imgLen d γ_core k =
      regWidth k + k + k * imgLen k + h2Rows d γ_core k * k := rfl
  simp only [packSeedWords, List.length_append, List.length_ofFn, hrw]
  omega

private theorem packSeedWords_injective {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ} :
    Function.Injective (packSeedWords (imgLen := imgLen) (d := d) (γ_core := γ_core)
      (k := k) (n := n) r) := by
  rintro ⟨x, h1, h2, pad⟩ ⟨x', h1', h2', pad'⟩ h
  dsimp [packSeedWords] at h
  have h4 := List.append_inj h (by simp)
  have h3 := List.append_inj h4.1 (by simp)
  have h2_eq := List.append_inj h3.1 (by simp)
  have h1_eq := List.append_inj h2_eq.1 rfl
  ext <;> simp_all [List.ofFn_inj]

/-- Embedding of `SeedTuple imgLen d γ_core k n` into `BitString n`. -/
private def packSeedEmb {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n) :
    SeedTuple imgLen d γ_core k n ↪ BitString n :=
  ⟨fun t => ofList n (packSeedWords r t), fun t t' h => by
    have h1 := congrArg List.ofFn h
    rw [ofFn_ofList (length_packSeedWords hr hfits t),
      ofFn_ofList (length_packSeedWords hr hfits t')] at h1
    exact packSeedWords_injective h1⟩

@[simp]
private theorem ofFn_packSeedEmb {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (t : SeedTuple imgLen d γ_core k n) :
    List.ofFn (packSeedEmb hr hfits t) = packSeedWords r t :=
  ofFn_ofList (length_packSeedWords hr hfits t)

/-- Evaluating `rawGen` on a packed seed recovers the exact concatenation of `pad`, `h1`,
`wordHash l1 h1 (g x)`, `h2`, and `wordHash (l2 + mActual) h2 x`. -/
private theorem rawGen_packSeedWords (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ n r : ℕ)
    (hr : r ≤ GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n)
    (t : SeedTuple imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) n) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    rawGen g imgLen d γ_core γ (packSeedWords r t) =
      List.ofFn t.2.2.2 ++ List.ofFn t.2.1 ++
        LinearHash.wordHash (l1Val d k r) (List.ofFn t.2.1) (g (List.ofFn t.1)) ++
        List.ofFn t.2.2.1 ++
        LinearHash.wordHash (l2Val d k r + mActual d γ k n)
          (List.ofFn t.2.2.1) (List.ofFn t.1) := by
  intro k
  set w := regWidth k
  let u0 := binaryWord w r
  let u1 := List.ofFn t.1
  let u2 := List.ofFn t.2.1
  let u3 := List.ofFn t.2.2.1
  let u4 := List.ofFn t.2.2.2
  have hu0 : u0.length = w := length_binaryWord (lt_two_pow_regWidth hr)
  have hu1 : u1.length = k := List.length_ofFn
  have hu2 : u2.length = k * imgLen k := List.length_ofFn
  have hu3 : u3.length = h2Rows d γ_core k * k := List.length_ofFn
  have hlen : (packSeedWords r t).length = n := length_packSeedWords hr hfits t
  have hpack : packSeedWords r t = u0 ++ (u1 ++ (u2 ++ (u3 ++ u4))) := by
    simp [packSeedWords, u0, u1, u2, u3, u4, w, k, List.append_assoc]
  have htake0 : (packSeedWords r t).take w = u0 := by
    rw [hpack, List.take_left' hu0]
  have hr_dec : boundedBinaryValue k ((packSeedWords r t).take w) = r := by
    rw [htake0, boundedBinaryValue_eq, binaryValue_binaryWord, Nat.min_eq_right hr]
  have hdrop0 : (packSeedWords r t).drop w = u1 ++ (u2 ++ (u3 ++ u4)) := by
    rw [hpack, List.drop_left' hu0]
  have htake1 : ((packSeedWords r t).drop w).take k = u1 := by
    rw [hdrop0, List.take_left' hu1]
  have hdrop1 : (packSeedWords r t).drop (w + k) = u2 ++ (u3 ++ u4) := by
    rw [← List.drop_drop, hdrop0, List.drop_left' hu1]
  have htake2 : ((packSeedWords r t).drop (w + k)).take (k * imgLen k) = u2 := by
    rw [hdrop1, List.take_left' hu2]
  have hdrop2 : (packSeedWords r t).drop (w + k + k * imgLen k) = u3 ++ u4 := by
    rw [← List.drop_drop, hdrop1, List.drop_left' hu2]
  have htake3 :
      ((packSeedWords r t).drop (w + k + k * imgLen k)).take (h2Rows d γ_core k * k) = u3 := by
    rw [hdrop2, List.take_left' hu3]
  have hdrop3 : (packSeedWords r t).drop (coreSeedLen imgLen d γ_core k) = u4 := by
    change (packSeedWords r t).drop (w + k + k * imgLen k + h2Rows d γ_core k * k) = u4
    rw [← List.drop_drop, hdrop2, List.drop_left' hu3]
  unfold rawGen
  dsimp only
  rw [hlen]
  change (packSeedWords r t).drop (coreSeedLen imgLen d γ_core k) ++
    ((packSeedWords r t).drop (w + k)).take (k * imgLen k) ++
    LinearHash.wordHash (l1Val d k (boundedBinaryValue k ((packSeedWords r t).take w)))
      (((packSeedWords r t).drop (w + k)).take (k * imgLen k))
      (g (((packSeedWords r t).drop w).take k)) ++
    ((packSeedWords r t).drop (w + k + k * imgLen k)).take (h2Rows d γ_core k * k) ++
    LinearHash.wordHash
      (l2Val d k (boundedBinaryValue k ((packSeedWords r t).take w)) + mActual d γ k n)
      (((packSeedWords r t).drop (w + k + k * imgLen k)).take (h2Rows d γ_core k * k))
      (((packSeedWords r t).drop w).take k) = _
  rw [hr_dec, htake1, htake2, htake3, hdrop3]

/-- Conditioning event $E_n \subseteq \mathrm{BitString}\; n$ at seed length $n$
([Liu and Pass, Proof of Theorem 5.5, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]). -/
private noncomputable def condSeedSet (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (r : ∀ k, Fin (k + 1)) (n : ℕ) :
    Finset (BitString n) := by
  classical
  let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  exact if hfits : coreSeedLen imgLen d γ_core k ≤ n then
    (S k ×ˢ (Finset.univ : Finset (RestTuple imgLen d γ_core k n))).map
      (packSeedEmb (Nat.le_of_lt_succ (r k).isLt) hfits)
  else Finset.univ

private theorem condSeedSet_nonempty (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) (n : ℕ) :
    (condSeedSet imgLen d γ_core S r n).Nonempty := by
  unfold condSeedSet
  dsimp only
  split_ifs
  · exact Finset.map_nonempty.mpr ((hS _).product Finset.univ_nonempty)
  · exact Finset.univ_nonempty

/-- When `coreSeedLen k ≤ n`, sampling uniformly from `condSeedSet ... n` and converting to
`List Bool` is identical to sampling `x ← uniformOfFinset (S k)` and independent uniform
`h1, h2, pad` and applying `packSeedWords (r k).val`. -/
private theorem uniformOfFinset_condSeedSet_map_ofFn (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) {n : ℕ}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    (PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn =
      (PMF.uniformOfFinset (S k) (hS k)).bind fun x =>
        (PMF.uniformOfFintype (BitString (k * imgLen k))).bind fun h1 =>
          (PMF.uniformOfFintype (BitString (h2Rows d γ_core k * k))).bind fun h2 =>
            (PMF.uniformOfFintype (BitString (n - coreSeedLen imgLen d γ_core k))).map fun pad =>
              packSeedWords (r k).val (x, h1, h2, pad) := by
  classical
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  have hcond : condSeedSet imgLen d γ_core S r n =
      (S k ×ˢ (Finset.univ : Finset (RestTuple imgLen d γ_core k n))).map
        (packSeedEmb (Nat.le_of_lt_succ (r k).isLt) hfits) := by
    unfold condSeedSet
    dsimp only
    exact dite_eq_left hfits
  have hpmf : PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n) =
      (PMF.uniformOfFinset (S k ×ˢ (Finset.univ : Finset (RestTuple imgLen d γ_core k n)))
        ((hS k).product Finset.univ_nonempty)).map
          (packSeedEmb (Nat.le_of_lt_succ (r k).isLt) hfits) := by
    rw [← uniformOfFinset_map (hs := (hS k).product Finset.univ_nonempty)]
    congr 1
  rw [hpmf, PMF.map_comp, uniformOfFinset_product_univ (hs := hS k)]
  simp only [RestTuple, ← PMF.uniformOfFintype_prod, PMF.map_bind, PMF.map_comp,
    Function.comp_def, ofFn_packSeedEmb]

/-! ### Leftover hash statistical distance and conditional entropy preservation -/

/-- Any initial row prefix of a flat uniform Boolean matrix is two-universal. -/
private theorem isTwoUniversal_block_prefix {n m count : ℕ} (h : m ≤ count) :
    IsTwoUniversal (PMF.uniformOfFintype (BitString (count * n)))
      (fun matrix => LinearHash.hash (block matrix ∘ Fin.castLE h)) := by
  refine IsUniversalHash.precompose_seed _ (blocksEquiv (m := count) (k := n))
    (hash := fun rows => LinearHash.hash (rows ∘ Fin.castLE h)) ?_
  rw [uniformOfFintype_map_equiv]
  exact LinearHash.isTwoUniversal_prefix h

/-- Conditional leftover hash bound on the preimage fibers of a regularity bucket $S_{k, r}$:
replacing `hash2 h2 x` (where $x \leftarrow S_{k, r}$ is resampled from the fiber of $x_0$) with
an independent uniform $m_2$-bit string changes the joint distribution with $(x_0, h_2)$ by at most
`if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2`. -/
private theorem dist_seededHash_regularityBucket_fiber_le {k m2 c2 : ℕ} {Image : Type*}
    [DecidableEq Image] (f : BitString k → Image) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty) (hm2 : m2 ≤ c2) :
    haveI (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    let side := PMF.uniformOfFinset (regularityBucket f r) hS
    let source (x₀ : BitString k) :=
      (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map Subtype.val
    let seed2 := PMF.uniformOfFintype (BitString (c2 * k))
    let hash2 (h2 : BitString (c2 * k)) (x : BitString k) : BitString m2 :=
      LinearHash.hash (block h2 ∘ Fin.castLE hm2) x
    dist (side.bind fun x₀ => (seededHash seed2 (source x₀) hash2).map (x₀, ·))
      (side.bind fun x₀ =>
        (seed2.bind fun h2 => (PMF.uniformOfFintype (BitString m2)).map (h2, ·)).map (x₀, ·)) ≤
      if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2 := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  intro side source seed2 hash2
  split_ifs with hm2_zero
  · subst m2
    have hsub : Subsingleton (BitString 0) := inferInstanceAs (Subsingleton (Fin 0 → Bool))
    have heq : (side.bind fun x₀ => (seededHash seed2 (source x₀) hash2).map (x₀, ·)) =
        (side.bind fun x₀ =>
          (seed2.bind fun h2 => (PMF.uniformOfFintype (BitString 0)).map (h2, ·)).map (x₀, ·)) := by
      congr 1; funext x₀
      rw [seededHash_eq_uniform_of_subsingleton]
    rw [heq, dist_self]
  · have hhash2 : IsTwoUniversal seed2 hash2 := isTwoUniversal_block_prefix hm2
    have hcond := hhash2.leftover_hash_conditional side source
    refine hcond.trans (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num))
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hpoint : ∀ x₀ : BitString k,
        (side x₀).toReal * collisionProbability (source x₀) ≤
          (side x₀).toReal * ((2 : ℝ) ^ r.val)⁻¹ := by
      intro x₀
      by_cases hx₀ : x₀ ∈ regularityBucket f r
      · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [collisionProbability_map_of_injective _ _ Subtype.val_injective,
          collisionProbability_uniform, ← Nat.card_eq_fintype_card]
        have hfib := (card_fiber_of_mem_regularityBucket f r hx₀).1
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hfib)
      · have h0 : side x₀ = 0 := by
          simp [side, PMF.uniformOfFinset_apply, hx₀]
        simp [h0]
    calc
      ∑ x₀ : BitString k, (side x₀).toReal * collisionProbability (source x₀)
        ≤ ∑ x₀ : BitString k, (side x₀).toReal * ((2 : ℝ) ^ r.val)⁻¹ :=
          Finset.sum_le_sum fun x₀ _ => hpoint x₀
      _ = (∑ x₀ : BitString k, (side x₀).toReal) * ((2 : ℝ) ^ r.val)⁻¹ :=
          (Finset.sum_mul _ _ _).symm
      _ = ((2 : ℝ) ^ r.val)⁻¹ := by rw [PMF.sum_toReal, one_mul]

/-- Taking the first `a ≤ count` bits of `LinearHash.wordHash count` gives
`LinearHash.wordHash a`. -/
private theorem wordHash_take {a count : ℕ} (h : a ≤ count) (seed input : List Bool) :
    (LinearHash.wordHash count seed input).take a = LinearHash.wordHash a seed input := by
  simp only [LinearHash.wordHash, listRows, ← List.map_take, List.take_range,
    Nat.min_eq_left h]

/-- `LinearHash.wordHash (a + 1)` appends the `a`-th inner-product bit to
`LinearHash.wordHash a`. -/
private theorem wordHash_succ (a : ℕ) (seed input : List Bool) :
    LinearHash.wordHash (a + 1) seed input =
      LinearHash.wordHash a seed input ++
        [((listRow input.length a seed).zipWith Bool.and input).foldl Bool.xor false] := by
  simp [LinearHash.wordHash, listRows, List.range_succ]

/-- On `BitString` inputs, `LinearHash.wordHash m` with `m ≤ count` agrees with
`LinearHash.hash` on the first `m` block rows of the seed matrix. -/
private theorem wordHash_ofFn_prefix {k m count : ℕ} (hm : m ≤ count)
    (matrix : BitString (count * k)) (x : BitString k) :
    LinearHash.wordHash m (List.ofFn matrix) (List.ofFn x) =
      List.ofFn (LinearHash.hash (block matrix ∘ Fin.castLE hm) x) := by
  rw [LinearHash.wordHash_eq_ofFn, block_ofList_prefix hm, ofList_ofFn]

private theorem l2Val_le_h2Rows (d γ_core k r : ℕ) :
    l2Val d k r ≤ h2Rows d γ_core k :=
  (l2Val_le d k r).trans (Nat.le_add_right k _)

private theorem lhlPrefixLen_le_output (d γ k n : ℕ) :
    lhlPrefixLen d k n ≤ n + γ * Nat.log 2 n := by
  unfold lhlPrefixLen
  omega

private theorem lhlPrefixLen_split (imgLen : ℕ → ℕ) (d γ_core : ℕ) {k n : ℕ} (r : ℕ)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (hk : 2 * (d * Nat.log 2 k) ≤ k) :
    (n - coreSeedLen imgLen d γ_core k) + k * imgLen k + l1Val d k r +
      h2Rows d γ_core k * k + l2Val d k r = lhlPrefixLen d k n := by
  have hl12 := l1Val_add_l2Val d k r
  have hcs : coreSeedLen imgLen d γ_core k =
      (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
  unfold lhlPrefixLen
  omega

/-- Core leftover-hash tuple distribution at input length `k` on regularity bucket $S_{k, r}$:
samples $x \leftarrow S_{k, r}$, $h_1$, $h_2$ uniformly and outputs
$((h_1, \mathrm{hash}_1(h_1, f(x))), (h_2, \mathrm{hash}_2(h_2, x)))$. -/
private noncomputable def coreLHLDist {k imgLen_k m1 m2 c2 : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty) (hm1 : m1 ≤ k) (hm2 : m2 ≤ c2) :
    PMF ((BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :=
  (PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x =>
    (PMF.uniformOfFintype (BitString (k * imgLen_k))).bind fun h1 =>
      (PMF.uniformOfFintype (BitString (c2 * k))).map fun h2 =>
        ((h1, LinearHash.hash (block h1 ∘ Fin.castLE hm1) (f x)),
          (h2, LinearHash.hash (block h2 ∘ Fin.castLE hm2) x))

/-- Ideal uniform core tuple distribution matching `coreLHLDist`. -/
private noncomputable def unifCoreDist (k imgLen_k m1 m2 c2 : ℕ) :
    PMF ((BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :=
  ((PMF.uniformOfFintype (BitString (k * imgLen_k))).bind fun h1 =>
    (PMF.uniformOfFintype (BitString m1)).map (h1, ·)).bind fun p1 =>
      ((PMF.uniformOfFintype (BitString (c2 * k))).bind fun h2 =>
        (PMF.uniformOfFintype (BitString m2)).map fun d2 => (p1, (h2, d2)))

/-- Statistical distance between `coreLHLDist` and `unifCoreDist` is bounded by the sum of the
fiber leftover-hash error on $x$ and the image leftover-hash error on $f(x)$
([Liu and Pass, Lemma 5.1, §5.3, p. 14 and Appendix A, pp. 21–22 of
arXiv:2009.11514v1][LiuPass2020]). -/
private theorem dist_coreLHLDist_unifCoreDist_le {k imgLen_k m1 m2 c2 : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (hm1 : m1 ≤ k) (hm2 : m2 ≤ c2) :
    dist (coreLHLDist f r hS hm1 hm2) (unifCoreDist k imgLen_k m1 m2 c2) ≤
      (if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2) +
        Real.sqrt ((2 : ℝ) ^ m1 * ((2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ k)) / 2 := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  let side := PMF.uniformOfFinset (regularityBucket f r) hS
  let source (x₀ : BitString k) :=
    (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map Subtype.val
  let seed1 := PMF.uniformOfFintype (BitString (k * imgLen_k))
  let seed2 := PMF.uniformOfFintype (BitString (c2 * k))
  let hash1 (h1 : BitString (k * imgLen_k)) (y : BitString imgLen_k) : BitString m1 :=
    LinearHash.hash (block h1 ∘ Fin.castLE hm1) y
  let hash2 (h2 : BitString (c2 * k)) (x : BitString k) : BitString m2 :=
    LinearHash.hash (block h2 ∘ Fin.castLE hm2) x
  let unif2 := seed2.bind fun h2 => (PMF.uniformOfFintype (BitString m2)).map (h2, ·)
  let stepF (xhd2 : BitString k × (BitString (c2 * k) × BitString m2)) :=
    seed1.map fun h1 => ((h1, hash1 h1 (f xhd2.1)), xhd2.2)
  let midCore := (side.bind fun x₀ => unif2.map (x₀, ·)).bind stepF
  have hcore_eq : coreLHLDist f r hS hm1 hm2 =
      (side.bind fun x₀ => (seededHash seed2 (source x₀) hash2).map (x₀, ·)).bind stepF := by
    unfold coreLHLDist
    conv_lhs => rw [← bind_regularityBucket_fiber_eq f r hS]
    change ((side.bind source).bind fun x => seed1.bind fun h1 =>
      seed2.map fun h2 => ((h1, hash1 h1 (f x)), (h2, hash2 h2 x))) = _
    rw [PMF.bind_bind, PMF.bind_bind]
    congr 1; funext x₀
    simp only [source, seededHash, stepF, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      Function.comp_def, PMF.bind_bind]
    have hinner (x : { x : BitString k // f x = f x₀ }) :
        (seed1.bind fun h1 =>
          seed2.map fun h2 => ((h1, hash1 h1 (f x.val)), (h2, hash2 h2 x.val))) =
        seed2.bind fun h2 =>
          seed1.map fun h1 => ((h1, hash1 h1 (f x₀)), (h2, hash2 h2 x.val)) := by
      rw [x.property]
      exact PMF.bind_comm seed1 seed2
        (fun h1 h2 => PMF.pure ((h1, hash1 h1 (f x₀)), (h2, hash2 h2 x.val)))
    simp_rw [hinner]
    exact PMF.bind_comm _ seed2 _
  have hdist1 : dist (coreLHLDist f r hS hm1 hm2) midCore ≤
      if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2 := by
    rw [hcore_eq]
    exact (PMF.dist_bind_le _ _ stepF).trans
      (dist_seededHash_regularityBucket_fiber_le f r hS hm2)
  have hmid_eq : midCore =
      (seededHash seed1 (side.map f) hash1).bind fun p1 => unif2.map (p1, ·) := by
    simp only [midCore, stepF, seededHash, PMF.bind_bind, PMF.bind_map,
      PMF.map_comp, Function.comp_def]
    have hinner (a : BitString k) :
        (unif2.bind fun x => seed1.map fun h1 => ((h1, hash1 h1 (f a)), x)) =
          seed1.bind fun h1 => unif2.map fun x => ((h1, hash1 h1 (f a)), x) :=
      PMF.bind_comm unif2 seed1 (fun x h1 => PMF.pure ((h1, hash1 h1 (f a)), x))
    simp_rw [hinner]
    exact PMF.bind_comm side seed1 _
  have hunif_eq : unifCoreDist k imgLen_k m1 m2 c2 =
      (seed1.bind fun h1 => (PMF.uniformOfFintype (BitString m1)).map (h1, ·)).bind
        fun p1 => unif2.map (p1, ·) := by
    simp [unifCoreDist, seed1, seed2, unif2, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hhash1 : IsTwoUniversal seed1 hash1 := isTwoUniversal_block_prefix hm1
  have hdist2 : dist midCore (unifCoreDist k imgLen_k m1 m2 c2) ≤
      Real.sqrt ((2 : ℝ) ^ m1 * ((2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ k)) / 2 := by
    rw [hmid_eq, hunif_eq]
    refine (PMF.dist_bind_le _ _ (fun p1 => unif2.map (p1, ·))).trans ?_
    have hlhl1 := hhash1.leftover_hash_of_mass_le (side.map f)
      (mass_map_regularityBucket_le f r hS hdense)
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using hlhl1
  exact (dist_triangle _ midCore _).trans (add_le_add hdist1 hdist2)

/-- Under the regularity gap `r.val + d * Nat.log 2 k ≤ k`, the statistical distance between
`coreLHLDist` (with $m_1 = \mathrm{l1Val}\; d\; k\; r$ and $m_2 = \mathrm{l2Val}\; d\; k\; r$)
and `unifCoreDist` is at most $\sqrt{2 (k + 1) / 2^{d \lfloor \log_2 k \rfloor}}$. -/
private theorem dist_coreLHLDist_unifCoreDist_le_of_gap {k imgLen_k d γ_core : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (hgap : r.val + d * Nat.log 2 k ≤ k) :
    dist (coreLHLDist f r hS (l1Val_le d k r.val) (l2Val_le_h2Rows d γ_core k r.val))
      (unifCoreDist k imgLen_k (l1Val d k r.val) (l2Val d k r.val) (h2Rows d γ_core k)) ≤
      Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
  have hbase := dist_coreLHLDist_unifCoreDist_le f r hS hdense (l1Val_le d k r.val)
    (l2Val_le_h2Rows d γ_core k r.val)
  have hterm1 :
      (if l2Val d k r.val = 0 then 0
        else Real.sqrt ((2 : ℝ) ^ (l2Val d k r.val) / (2 : ℝ) ^ r.val) / 2) ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) / 2 := by
    split_ifs with hm2
    · positivity
    · refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
      have hl2_eq := l2Val_eq_of_gap hgap
      have hr_split : l2Val d k r.val + d * Nat.log 2 k = r.val := by omega
      have hpow : (2 : ℝ) ^ r.val = (2 : ℝ) ^ (l2Val d k r.val) * (2 : ℝ) ^ (d * Nat.log 2 k) := by
        rw [← pow_add, hr_split]
      rw [hpow, div_mul_eq_div_div, div_self (by positivity), one_div]
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (by positivity) (by linarith)
  have hterm2 :
      Real.sqrt ((2 : ℝ) ^ (l1Val d k r.val) *
        ((2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ k)) / 2 ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) / 2 := by
    refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
    have hl1_le : l1Val d k r.val + r.val + d * Nat.log 2 k ≤ k := by
      have := l1Val_add_le_of_gap hgap
      omega
    have hpow : (2 : ℝ) ^ (l1Val d k r.val) * (2 : ℝ) ^ r.val * (2 : ℝ) ^ (d * Nat.log 2 k) ≤
        (2 : ℝ) ^ k := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hl1_le
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      (2 : ℝ) ^ (l1Val d k r.val) * (2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) *
          (2 : ℝ) ^ (d * Nat.log 2 k)
        = 2 * (k + 1 : ℝ) *
            ((2 : ℝ) ^ (l1Val d k r.val) * (2 : ℝ) ^ r.val * (2 : ℝ) ^ (d * Nat.log 2 k)) := by
          ring
      _ ≤ 2 * (k + 1 : ℝ) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  linarith [hbase, hterm1, hterm2]

private theorem bind_uniformOfFintype_append (a b : ℕ) :
    ((uniformList a).bind fun u =>
      (PMF.uniformOfFintype (BitString b)).map fun v => u ++ List.ofFn v) =
      uniformList (a + b) := by
  rw [uniformList_add]
  simp [uniformList, PMF.map_comp, Function.comp_def]

private theorem uniformOfFintype_five_append (n0 n1 n2 n3 n4 : ℕ) :
    ((PMF.uniformOfFintype (BitString n0)).bind fun u0 =>
      (PMF.uniformOfFintype (BitString n1)).bind fun u1 =>
        (PMF.uniformOfFintype (BitString n2)).bind fun u2 =>
          (PMF.uniformOfFintype (BitString n3)).bind fun u3 =>
            (PMF.uniformOfFintype (BitString n4)).map fun u4 =>
              List.ofFn u0 ++ List.ofFn u1 ++ List.ofFn u2 ++ List.ofFn u3 ++ List.ofFn u4) =
      uniformList (n0 + n1 + n2 + n3 + n4) := by
  have h0 : (PMF.uniformOfFintype (BitString n0)).map List.ofFn = uniformList n0 := rfl
  rw [← bind_uniformOfFintype_append, ← bind_uniformOfFintype_append,
    ← bind_uniformOfFintype_append, ← bind_uniformOfFintype_append, ← h0]
  simp [PMF.bind_map, PMF.bind_bind, Function.comp_def]

private theorem bind_four_comm_fifth {α₁ α₂ α₃ α₄ α₅ β : Type*}
    (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄) (p₅ : PMF α₅)
    (F : α₁ → α₂ → α₃ → α₄ → α₅ → β) :
    (p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ => p₄.bind fun a₄ =>
      p₅.map fun a₅ => F a₁ a₂ a₃ a₄ a₅) =
    (p₅.bind fun a₅ => p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ =>
      p₄.map fun a₄ => F a₁ a₂ a₃ a₄ a₅) := by
  rw [PMF.bind_comm p₅ p₁]
  congr 1; funext a₁
  rw [PMF.bind_comm p₅ p₂]
  congr 1; funext a₂
  rw [PMF.bind_comm p₅ p₃]
  congr 1; funext a₃
  exact PMF.bind_comm p₄ p₅ (fun a₄ a₅ => PMF.pure (F a₁ a₂ a₃ a₄ a₅))

private theorem uniformList_map_ofList (m : ℕ) :
    (uniformList m).map (ofList m) = PMF.uniformOfFintype (BitString m) := by
  unfold uniformList
  rw [PMF.map_comp]
  have hid : ofList m ∘ (List.ofFn : BitString m → List Bool) = id := by
    funext x; exact ofList_ofFn x
  rw [hid, PMF.map_id]

private theorem ofList_take_eq_ofList (m : ℕ) (w : List Bool) :
    ofList m (w.take m) = ofList m w := by
  funext i
  simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]

private theorem ofList_ofFn_ofList_of_le {m L : ℕ} (h : m ≤ L) (w : List Bool) :
    ofList m (List.ofFn (ofList L w)) = ofList m w := by
  funext i
  simp [ofList, List.getD_eq_getElem?_getD, lt_of_lt_of_le i.isLt h]

private theorem map_bind_four_eq_bind_three_map {α₁ α₂ α₃ α₄ β γ δ : Type*}
    (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄)
    (F₁ : α₁ → α₂ → α₃ → α₄ → β) (F₂ : β → γ)
    (G₁ : α₁ → α₂ → α₃ → δ) (G₂ : δ → α₄ → γ)
    (hFG : ∀ x₁ x₂ x₃ x₄, F₂ (F₁ x₁ x₂ x₃ x₄) = G₂ (G₁ x₁ x₂ x₃) x₄) :
    (p₁.bind fun x₁ => p₂.bind fun x₂ => p₃.bind fun x₃ => p₄.map fun x₄ => F₁ x₁ x₂ x₃ x₄).map F₂ =
      (p₁.bind fun x₁ => p₂.bind fun x₂ => p₃.map fun x₃ => G₁ x₁ x₂ x₃).bind
        (fun c => p₄.map fun x₄ => G₂ c x₄) := by
  simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def]
  congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃; congr 1; funext x₄
  exact hFG x₁ x₂ x₃ x₄

private theorem unifCoreDist_bind_packLHL (k imgLen_k m1 m2 c2 padLen m_lhl : ℕ)
    (hlen : padLen + k * imgLen_k + m1 + c2 * k + m2 = m_lhl) :
    (unifCoreDist k imgLen_k m1 m2 c2).bind
      (fun c => (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
        ofList m_lhl (List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
          List.ofFn c.2.1 ++ List.ofFn c.2.2)) =
      PMF.uniformOfFintype (BitString m_lhl) := by
  have h1 : (unifCoreDist k imgLen_k m1 m2 c2).bind
      (fun c => (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
        ofList m_lhl (List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
          List.ofFn c.2.1 ++ List.ofFn c.2.2)) =
    ((PMF.uniformOfFintype (BitString padLen)).bind fun pad =>
      (PMF.uniformOfFintype (BitString (k * imgLen_k))).bind fun h1 =>
        (PMF.uniformOfFintype (BitString m1)).bind fun d1 =>
          (PMF.uniformOfFintype (BitString (c2 * k))).bind fun h2 =>
            (PMF.uniformOfFintype (BitString m2)).map fun d2 =>
              List.ofFn pad ++ List.ofFn h1 ++ List.ofFn d1 ++
                List.ofFn h2 ++ List.ofFn d2).map (ofList m_lhl) := by
    simp only [unifCoreDist, PMF.bind_bind, PMF.bind_map, PMF.map_bind,
      PMF.map_comp, Function.comp_def]
    exact bind_four_comm_fifth _ _ _ _ _ _
  rw [h1, uniformOfFintype_five_append, hlen, uniformList_map_ofList]

/-- Conditional entropy preservation for `fullGen` on `condSeedSet`:
when `coreLHLDist` is within `1 / (lhlPrefixLen d k n) ^ 2` of `unifCoreDist`, the Shannon
entropy of `fullGen` on `condSeedSet` is at least `lhlPrefixLen d k n - 2`
([Liu and Pass, Proof of Theorem 5.5, §5.3, p. 15 and Lemma 2.2, §2.5, p. 9 of
arXiv:2009.11514v1][LiuPass2020]). -/
private theorem entropy_fullGen_condSeedSet_ge (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ : ℕ) (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) {n : ℕ}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n)
    (hk_2d : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hg_len : ∀ x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n),
      (g (List.ofFn x)).length =
        imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
    (hS_eq : S (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =
      regularityBucket
        (fun x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =>
          ofList (imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
            (g (List.ofFn x)))
        (r (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)))
    (hdist :
      let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
      let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
      dist (coreLHLDist f (r k) (hS_eq ▸ hS k) (l1Val_le d k (r k).val)
          (l2Val_le_h2Rows d γ_core k (r k).val))
        (unifCoreDist k (imgLen k) (l1Val d k (r k).val) (l2Val d k (r k).val)
          (h2Rows d γ_core k)) ≤ 1 / (lhlPrefixLen d k n : ℝ) ^ 2) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    ((lhlPrefixLen d k n : ℝ) - 2) ≤
      PMF.entropy ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
          ofList (n + γ * Nat.log 2 n) (fullGen g imgLen d γ_core γ (List.ofFn x))) := by
  intro k
  let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
  have hS_reg : (regularityBucket f (r k)).Nonempty := hS_eq ▸ hS k
  let m_lhl := lhlPrefixLen d k n
  let L := n + γ * Nat.log 2 n
  let padLen := n - coreSeedLen imgLen d γ_core k
  let m1 := l1Val d k (r k).val
  let m2 := l2Val d k (r k).val
  let c2 := h2Rows d γ_core k
  let D_seed := (PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
    (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn
  let D_out := D_seed.map fun z => ofList L (fullGen g imgLen d γ_core γ z)
  let D_lhl := D_seed.map fun z => ofList m_lhl ((fullGen g imgLen d γ_core γ z).take m_lhl)
  have hent_mono : D_lhl.entropy ≤
      ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
          ofList L (fullGen g imgLen d γ_core γ (List.ofFn x))).entropy := by
    have hmap_out : ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
          ofList L (fullGen g imgLen d γ_core γ (List.ofFn x))) = D_out := by
      simp [D_out, D_seed, PMF.map_comp, Function.comp_def]
    have hmap_lhl : D_lhl = D_out.map (fun y : BitString L => ofList m_lhl (List.ofFn y)) := by
      simp only [D_lhl, D_out, PMF.map_comp, Function.comp_def]
      congr 1; funext z
      rw [ofList_take_eq_ofList, ofList_ofFn_ofList_of_le (lhlPrefixLen_le_output d γ k n)]
    rw [hmap_out, hmap_lhl]
    exact PMF.entropy_map_le D_out _
  let packLHL
      (c : (BitString (k * imgLen k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :
      PMF (BitString m_lhl) :=
    (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
      ofList m_lhl (List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
        List.ofFn c.2.1 ++ List.ofFn c.2.2)
  have hreal_lhl : D_lhl =
      (coreLHLDist f (r k) hS_reg (l1Val_le d k (r k).val)
        (l2Val_le_h2Rows d γ_core k (r k).val)).bind packLHL := by
    have hcond_seed : D_seed =
        (PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x =>
          (PMF.uniformOfFintype (BitString (k * imgLen k))).bind fun h1 =>
            (PMF.uniformOfFintype (BitString (c2 * k))).bind fun h2 =>
              (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
                packSeedWords (r k).val (x, h1, h2, pad) := by
      have h1 := uniformOfFinset_condSeedSet_map_ofFn imgLen d γ_core S hS r hfits
      dsimp only at h1
      have h2 : PMF.uniformOfFinset (S k) (hS k) =
          PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg := by
        congr 1
      dsimp [D_seed]
      rw [h1, h2]
    dsimp only [D_lhl, coreLHLDist, packLHL]
    rw [hcond_seed]
    refine map_bind_four_eq_bind_three_map _ _ _ _ _ _ _ _ fun x h1 h2 pad => ?_
    have hplen : (packSeedWords (r k).val (x, h1, h2, pad)).length = n :=
      length_packSeedWords (Nat.le_of_lt_succ (r k).isLt) hfits (x, h1, h2, pad)
    have hfits_z : coreSeedLen imgLen d γ_core
        (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
          (packSeedWords (r k).val (x, h1, h2, pad)).length) ≤
        (packSeedWords (r k).val (x, h1, h2, pad)).length := by
      rw [hplen]; exact hfits
    have hk_z : 2 * (d * Nat.log 2
        (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
          (packSeedWords (r k).val (x, h1, h2, pad)).length)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
          (packSeedWords (r k).val (x, h1, h2, pad)).length := by
      rw [hplen]; exact hk_2d
    rw [fullGen_eq_rawGen hfits_z hk_z,
      rawGen_packSeedWords g imgLen d γ_core γ n (r k).val
        (Nat.le_of_lt_succ (r k).isLt) hfits (x, h1, h2, pad)]
    set u := List.ofFn pad ++ List.ofFn h1 ++
      LinearHash.wordHash m1 (List.ofFn h1) (g (List.ofFn x)) ++ List.ofFn h2
    set v := LinearHash.wordHash (m2 + mActual d γ k n) (List.ofFn h2) (List.ofFn x)
    have hu_len : u.length = padLen + k * imgLen k + m1 + c2 * k := by
      simp [u, padLen, Nat.add_assoc]
    have hsplit : m_lhl = u.length + m2 := by
      rw [hu_len]
      exact (lhlPrefixLen_split imgLen d γ_core (r k).val hfits hk_2d).symm
    have htake : (u ++ v).take m_lhl = u ++ v.take m2 := by
      rw [hsplit, List.take_append]
      simp
    have hv_take : v.take m2 =
        List.ofFn (LinearHash.hash
          (block h2 ∘ Fin.castLE (l2Val_le_h2Rows d γ_core k (r k).val)) x) := by
      dsimp [v]
      rw [wordHash_take (Nat.le_add_right m2 _), wordHash_ofFn_prefix]
    have hg_fx : g (List.ofFn x) = List.ofFn (f x) := (ofFn_ofList (hg_len x)).symm
    have hu_d1 : LinearHash.wordHash m1 (List.ofFn h1) (g (List.ofFn x)) =
        List.ofFn (LinearHash.hash (block h1 ∘ Fin.castLE (l1Val_le d k (r k).val)) (f x)) := by
      rw [hg_fx, wordHash_ofFn_prefix]
    change ofList m_lhl ((u ++ v).take m_lhl) = _
    rw [htake, hv_take]
    dsimp [u]
    rw [hu_d1]
  have hunif_lhl : (unifCoreDist k (imgLen k) m1 m2 c2).bind packLHL =
      PMF.uniformOfFintype (BitString m_lhl) :=
    unifCoreDist_bind_packLHL k (imgLen k) m1 m2 c2 padLen m_lhl
      (lhlPrefixLen_split imgLen d γ_core (r k).val hfits hk_2d)
  have hdist_lhl : dist D_lhl (PMF.uniformOfFintype (BitString m_lhl)) ≤
      1 / (m_lhl : ℝ) ^ 2 := by
    rw [hreal_lhl, ← hunif_lhl]
    exact (PMF.dist_bind_le _ _ packLHL).trans hdist
  exact (entropy_ge_of_dist_uniform_le D_lhl hdist_lhl).trans hent_mono

/-! ### Goldreich–Levin hybrid reduction and PPT inverter -/

/-- Overwrite row `idx` of a flat `k`-column Boolean matrix word `h2` with `query`. -/
private def spliceMatrixWord (k idx : ℕ) (h2 query : List Bool) : List Bool :=
  h2.take (idx * k) ++ query ++ h2.drop ((idx + 1) * k)

@[local fun_prop]
private theorem computableTidilyInPolyTime_spliceMatrixWord {α : Type} {encode : α ↪ List Bool}
    {k idx : α → ℕ} {h2 query : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hidx : ComputableTidilyInPolyTime idx encode encUnary)
    (hh2 : ComputableTidilyInPolyTime h2 encode encBits)
    (hquery : ComputableTidilyInPolyTime query encode encBits) :
    ComputableTidilyInPolyTime
      (fun a => spliceMatrixWord (k a) (idx a) (h2 a) (query a)) encode encBits := by
  unfold spliceMatrixWord
  fun_prop

/-- Assemble the word challenge fed to the PRG distinguisher at hybrid step `idx = m2 + j`. -/
private def wordChallenge (k m1 idx : ℕ) (pad h1 image h2 digest r_word z_tail query : List Bool) :
    List Bool :=
  pad ++ h1 ++ LinearHash.wordHash m1 h1 image ++
    spliceMatrixWord k idx h2 query ++ digest ++ r_word ++ z_tail

@[local fun_prop]
private theorem computableTidilyInPolyTime_wordChallenge {α : Type} {encode : α ↪ List Bool}
    {k m1 idx : α → ℕ} {pad h1 image h2 digest r_word z_tail query : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hm1 : ComputableTidilyInPolyTime m1 encode encUnary)
    (hidx : ComputableTidilyInPolyTime idx encode encUnary)
    (hpad : ComputableTidilyInPolyTime pad encode encBits)
    (hh1 : ComputableTidilyInPolyTime h1 encode encBits)
    (himage : ComputableTidilyInPolyTime image encode encBits)
    (hh2 : ComputableTidilyInPolyTime h2 encode encBits)
    (hdigest : ComputableTidilyInPolyTime digest encode encBits)
    (hr_word : ComputableTidilyInPolyTime r_word encode encBits)
    (hz_tail : ComputableTidilyInPolyTime z_tail encode encBits)
    (hquery : ComputableTidilyInPolyTime query encode encBits) :
    ComputableTidilyInPolyTime
      (fun a => wordChallenge (k a) (m1 a) (idx a) (pad a) (h1 a) (image a)
        (h2 a) (digest a) (r_word a) (z_tail a) (query a)) encode encBits := by
  unfold wordChallenge
  fun_prop

/-- Convert the saved-coin distinguisher into a signed parity predictor for row `idx` of `h2`. -/
private def wordStepPredictor (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (n k m1 idx : ℕ)
    (pad h1 image h2 digest r_word pol_word z_tail coins query : List Bool) : Bool :=
  let r_bit := r_word.headD false
  let pol := pol_word.headD false
  (if evaluate (n, wordChallenge k m1 idx pad h1 image h2 digest r_word z_tail query) coins then
    r_bit
  else !r_bit) ^^ pol

@[local fun_prop]
private theorem computableTidilyInPolyTime_wordStepPredictor {α : Type} {encode : α ↪ List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    {n k m1 idx : α → ℕ}
    {pad h1 image h2 digest r_word pol_word z_tail coins query : α → List Bool}
    (hevaluate : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hn : ComputableTidilyInPolyTime n encode encUnary)
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hm1 : ComputableTidilyInPolyTime m1 encode encUnary)
    (hidx : ComputableTidilyInPolyTime idx encode encUnary)
    (hpad : ComputableTidilyInPolyTime pad encode encBits)
    (hh1 : ComputableTidilyInPolyTime h1 encode encBits)
    (himage : ComputableTidilyInPolyTime image encode encBits)
    (hh2 : ComputableTidilyInPolyTime h2 encode encBits)
    (hdigest : ComputableTidilyInPolyTime digest encode encBits)
    (hr_word : ComputableTidilyInPolyTime r_word encode encBits)
    (hpol_word : ComputableTidilyInPolyTime pol_word encode encBits)
    (hz_tail : ComputableTidilyInPolyTime z_tail encode encBits)
    (hcoins : ComputableTidilyInPolyTime coins encode encBits)
    (hquery : ComputableTidilyInPolyTime query encode encBits) :
    ComputableTidilyInPolyTime
      (fun a => wordStepPredictor evaluate (n a) (k a) (m1 a) (idx a) (pad a) (h1 a)
        (image a) (h2 a) (digest a) (r_word a) (pol_word a) (z_tail a) (coins a) (query a))
      encode encBool := by
  unfold wordStepPredictor
  fun_prop

/-- Coin budget for the PRG distinguisher on an output of length `n + γ * Nat.log 2 n` at
security parameter `n`. -/
private def condCoinBudget (c_eval d_eval γ n : ℕ) : ℕ :=
  c_eval * (3 * n + γ * Nat.log 2 n + 2) ^ d_eval

@[local fun_prop]
private theorem computableTidilyInPolyTime_condCoinBudget {α : Type} {encode : α ↪ List Bool}
    (c_eval d_eval γ : ℕ) {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encode encUnary) :
    ComputableTidilyInPolyTime (fun a => condCoinBudget c_eval d_eval γ (n a))
      encode encUnary := by
  unfold condCoinBudget
  fun_prop

/-- Inner Goldreich–Levin inversion step: sample `h2`, `digest`, and `masks`, and run
`wordDecode`. -/
private noncomputable def innerGuessInverter (g : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core deg n k r_val j : ℕ)
    (pad h1 image r_word pol_word z_tail coins : List Bool) : ProbComp (List Bool) := do
  let h2 ← BitString.sampleList (h2Rows d γ_core k * k)
  let digest ← BitString.sampleList (l2Val d k r_val + j)
  let masks ← BitString.sampleList
    (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k) * k)
  return GoldreichLevin.wordDecode g
    (wordStepPredictor evaluate n k (l1Val d k r_val) (l2Val d k r_val + j)
      pad h1 image h2 digest r_word pol_word z_tail coins)
    deg k image masks

@[local fun_prop]
private theorem isPPTOn_innerGuessInverter {α : Type} {encode : α ↪ List Bool}
    {g : List Bool → List Bool} {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (d γ_core deg : ℕ)
    {n k r_val j : α → ℕ} {pad h1 image r_word pol_word z_tail coins : α → List Bool}
    (hg : ComputableTidilyInPolyTime g encBits encBits)
    (hevaluate : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hn : ComputableTidilyInPolyTime n encode encUnary)
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hr_val : ComputableTidilyInPolyTime r_val encode encUnary)
    (hj : ComputableTidilyInPolyTime j encode encUnary)
    (hpad : ComputableTidilyInPolyTime pad encode encBits)
    (hh1 : ComputableTidilyInPolyTime h1 encode encBits)
    (himage : ComputableTidilyInPolyTime image encode encBits)
    (hr_word : ComputableTidilyInPolyTime r_word encode encBits)
    (hpol_word : ComputableTidilyInPolyTime pol_word encode encBits)
    (hz_tail : ComputableTidilyInPolyTime z_tail encode encBits)
    (hcoins : ComputableTidilyInPolyTime coins encode encBits) :
    IsPPTOn encode encBits (fun a => innerGuessInverter g evaluate d γ_core deg
      (n a) (k a) (r_val a) (j a) (pad a) (h1 a) (image a)
      (r_word a) (pol_word a) (z_tail a) (coins a)) := by
  unfold innerGuessInverter
  fun_prop

/-- Sample the auxiliary hybrid randomness (`pad`, `h1`, `r_word`, `pol_word`, `z_tail`, `coins`)
and invoke `innerGuessInverter`. -/
private noncomputable def stepAuxInverter (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core γ c_eval d_eval deg k r_val n_offset j : ℕ)
    (image : List Bool) : ProbComp (List Bool) := do
  let pad ← BitString.sampleList n_offset
  let h1 ← BitString.sampleList (k * imgLen k)
  let r_word ← BitString.sampleList 1
  let pol_word ← BitString.sampleList 1
  let z_tail ← BitString.sampleList
    (mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) - (j + 1))
  let coins ← BitString.sampleList
    (condCoinBudget c_eval d_eval γ (coreSeedLen imgLen d γ_core k + n_offset))
  innerGuessInverter g evaluate d γ_core deg
    (coreSeedLen imgLen d γ_core k + n_offset) k r_val j pad h1 image r_word pol_word z_tail coins

@[local fun_prop]
private theorem isPPTOn_stepAuxInverter {α : Type} {encode : α ↪ List Bool}
    {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (d γ_core γ c_eval d_eval deg : ℕ)
    {k r_val n_offset j : α → ℕ} {image : α → List Bool}
    (hg : ComputableTidilyInPolyTime g encBits encBits)
    (himgLen : ComputableTidilyInPolyTime imgLen encUnary encUnary)
    (hevaluate : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hk : ComputableTidilyInPolyTime k encode encUnary)
    (hr_val : ComputableTidilyInPolyTime r_val encode encUnary)
    (hn_offset : ComputableTidilyInPolyTime n_offset encode encUnary)
    (hj : ComputableTidilyInPolyTime j encode encUnary)
    (himage : ComputableTidilyInPolyTime image encode encBits) :
    IsPPTOn encode encBits (fun a => stepAuxInverter g imgLen evaluate d γ_core γ
      c_eval d_eval deg (k a) (r_val a) (n_offset a) (j a) (image a)) := by
  unfold stepAuxInverter
  fun_prop

/-- Complete uniform PPT inverter reducing conditional PRG distinguishing to inverting `g`:
samples `r_val`, `n_offset`, and hybrid step `j` in dyadic ranges and runs `stepAuxInverter`. -/
private noncomputable def condInverter (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core γ c_eval d_eval deg : ℕ) : Inverter := fun k image => do
  let r_val ← ProbComp.sampleDyadicIndex (k + 1)
  let n_offset ← ProbComp.sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
  let j ← ProbComp.sampleDyadicIndex
    (mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset))
  stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_offset j image

private theorem isPPT_condInverter {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (hg : ComputableTidilyInPolyTime g encBits encBits)
    (himgLen : ComputableTidilyInPolyTime imgLen encUnary encUnary)
    (hevaluate : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (d γ_core γ c_eval d_eval deg : ℕ) :
    IsPPT encBits (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) := by
  unfold condInverter
  fun_prop

/-- Typed finite predictor matching `wordStepPredictor`. -/
private def stepPredictor (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (n k imgLen_k d γ_core r_val j : ℕ)
    (pad h1 r_word pol_word z_tail coins : List Bool)
    (image : BitString imgLen_k)
    (rows : Fin (h2Rows d γ_core k) → BitString k)
    (digest : BitString (l2Val d k r_val + j))
    (query : BitString k) : Bool :=
  wordStepPredictor evaluate n k (l1Val d k r_val) (l2Val d k r_val + j)
    pad h1 (List.ofFn image)
    (List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows))
    (List.ofFn digest) r_word pol_word z_tail coins (List.ofFn query)

/-- `innerGuessInverter` evaluates to `Pseudoentropy.guessInverter` mapped by `List.ofFn`. -/
private theorem eval_innerGuessInverter {k imgLen_k : ℕ}
    (g : List Bool → List Bool) (f : BitString k → BitString imgLen_k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core deg n r_val j : ℕ)
    (pad h1 r_word pol_word z_tail coins : List Bool) (image : BitString imgLen_k) :
    ProbComp.eval (innerGuessInverter g evaluate d γ_core deg n k r_val j
        pad h1 (List.ofFn image) r_word pol_word z_tail coins) =
      (Pseudoentropy.guessInverter f
        (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 r_word pol_word z_tail coins
          image)
        (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k))
        (GoldreichLevin.precision deg k) image).map List.ofFn := by
  have hmatrix : uniformList (h2Rows d γ_core k * k) =
      (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k)).map
        (fun rows => List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows)) := by
    rw [uniformList,
      ← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm,
      PMF.map_comp]
    rfl
  have hfunction : (fun bits : BitString k => g (List.ofFn bits)) =
      (List.ofFn : BitString imgLen_k → List Bool) ∘ f := funext hf
  have hdecode (predictor : List Bool → Bool) :
      (uniformList (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k) * k)).bind
        (fun masks => PMF.pure (GoldreichLevin.wordDecode g predictor deg k
          (List.ofFn image) masks)) =
      (GoldreichLevin.invertFixed f (fun query => predictor (List.ofFn query))
        (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k)) image).map List.ofFn := by
    change (uniformList _).map (GoldreichLevin.wordDecode g predictor deg k (List.ofFn image)) = _
    rw [GoldreichLevin.uniform_wordDecode, hfunction,
      GoldreichLevin.invertFixed_comp_injective f List.ofFn (fun _ _ h => List.ofFn_inj.mp h)]
  simp only [innerGuessInverter, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  simp_rw [hdecode, hmatrix]
  simp only [uniformList, PMF.bind_map, PMF.map_bind,
    Function.comp_def, Pseudoentropy.guessInverter]
  rfl

/-- Splicing row `idx` in a flat matrix word agrees with `Function.update` on the block rows. -/
private theorem spliceMatrixWord_eq_ofFn_update {m k : ℕ} (rows : Fin m → BitString k)
    (idx : Fin m) (query : BitString k) :
    spliceMatrixWord k idx.val
        (List.ofFn ((blocksEquiv (m := m) (k := k)).symm rows)) (List.ofFn query) =
      List.ofFn ((blocksEquiv (m := m) (k := k)).symm (Function.update rows idx query)) := by
  set w := List.ofFn ((blocksEquiv (m := m) (k := k)).symm rows)
  set v := spliceMatrixWord k idx.val w (List.ofFn query)
  have hw_len : w.length = m * k := List.length_ofFn
  have hidx_le : (idx.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k idx.isLt
  have hv_len : v.length = m * k := by
    simp only [v, spliceMatrixWord, List.length_append, List.length_take,
      List.length_drop, List.length_ofFn, hw_len]
    rw [Nat.add_mul, one_mul] at hidx_le ⊢
    omega
  have hrow (j : Fin m) :
      listBlock k v j.val = List.ofFn (Function.update rows idx query j) := by
    let u1 := w.take (idx.val * k)
    let u2 := List.ofFn query
    let u3 := w.drop ((idx.val + 1) * k)
    have hu1 : u1.length = idx.val * k := by
      simp only [u1, List.length_take, hw_len]
      rw [Nat.add_mul] at hidx_le
      omega
    have hu2 : u2.length = k := List.length_ofFn
    have hv_eq : v = u1 ++ (u2 ++ u3) := by simp [v, spliceMatrixWord, u1, u2, u3]
    rcases lt_trichotomy j.val idx.val with hlt | heq | hgt
    · have hj_ne : j ≠ idx := Fin.ne_of_val_ne hlt.ne
      have hj_mul : j.val * k + k ≤ idx.val * k := by
        have h1 : (j.val + 1) * k ≤ idx.val * k := Nat.mul_le_mul_right k hlt
        rwa [Nat.add_mul, one_mul] at h1
      have hdrop : v.drop (j.val * k) = u1.drop (j.val * k) ++ (u2 ++ u3) := by
        rw [hv_eq, List.drop_append_of_le_length (by omega)]
      have htake : (v.drop (j.val * k)).take k = (u1.drop (j.val * k)).take k := by
        rw [hdrop, List.take_append_of_le_length (by simp [hu1]; omega)]
      have hu1_drop : (u1.drop (j.val * k)).take k = listBlock k w j.val := by
        dsimp [u1, listBlock]
        rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
      have hw_block : listBlock k w j.val = List.ofFn (rows j) := by
        simpa [w] using listBlock_ofFn ((blocksEquiv (m := m) (k := k)).symm rows) j
      rw [Function.update_of_ne hj_ne, listBlock, htake, hu1_drop, hw_block]
    · have hj_eq : j = idx := Fin.ext heq
      subst hj_eq
      rw [Function.update_self, listBlock, hv_eq, List.drop_left' hu1, List.take_left' hu2]
    · have hj_ne : j ≠ idx := Fin.ne_of_val_ne hgt.ne'
      have hj_mul : (idx.val + 1) * k ≤ j.val * k := Nat.mul_le_mul_right k hgt
      have hu12 : (u1 ++ u2).length = (idx.val + 1) * k := by
        rw [List.length_append, hu1, hu2, Nat.add_mul, one_mul]
      have hv_eq' : v = (u1 ++ u2) ++ u3 := by simp [hv_eq, List.append_assoc]
      have hdrop : v.drop (j.val * k) = w.drop (j.val * k) := by
        rw [hv_eq', List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
        dsimp [u3]
        rw [hu12, List.drop_drop, Nat.add_sub_of_le hj_mul]
      have hw_block : listBlock k w j.val = List.ofFn (rows j) := by
        simpa [w] using listBlock_ofFn ((blocksEquiv (m := m) (k := k)).symm rows) j
      rw [Function.update_of_ne hj_ne, listBlock, hdrop, ← listBlock, hw_block]
  have hv_ofFn : v = List.ofFn (ofList (m * k) v) := (ofFn_ofList hv_len).symm
  have hblocks : ofList (m * k) v =
      (blocksEquiv (m := m) (k := k)).symm (Function.update rows idx query) := by
    apply (blocksEquiv (m := m) (k := k)).injective
    rw [blocksEquiv.apply_symm_apply]
    funext j
    apply List.ofFn_inj.mp
    rw [blocksEquiv_apply, ← listBlock_ofFn (ofList (m * k) v) j, ← hv_ofFn, hrow j]
  exact hv_ofFn.trans (congrArg List.ofFn hblocks)

private theorem update_comp_castLE_of_eq {c2 m_pre : ℕ} {α : Type*}
    (rows : Fin c2 → α) (idx : Fin c2) (query : α)
    (hlen : m_pre ≤ c2) (hidx : m_pre = idx.val) :
    Function.update rows idx query ∘ Fin.castLE hlen = rows ∘ Fin.castLE hlen := by
  funext i
  simp only [Function.comp_apply]
  have hne : (Fin.castLE hlen i).val ≠ idx.val := by
    simp only [Fin.val_castLE, ← hidx]
    exact ne_of_lt i.isLt
  exact Function.update_of_ne (Fin.ne_of_val_ne hne) _ _

/-- Averaging `2 * agreement - 1` over the random guess bit `r_bit : Bool` equals twice the
distinguishing gap between the target inner-product bit `x ⬝ᵥ query` and a uniform bit. -/
private theorem sum_bool_agreement_eq {k : ℕ} (evalBit : BitString k → Bool → Bool)
    (x : BitString k) :
    (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
      (2 * GoldreichLevin.agreement
        (fun query => if evalBit query r_bit then r_bit else !r_bit) x - 1)) =
    2 * ((((PMF.uniformOfFintype (BitString k)).map
          (fun query => evalBit query (x ⬝ᵥ query))) true).toReal -
        (((PMF.uniformOfFintype (BitString k)).bind fun query =>
          (PMF.uniformOfFintype Bool).map (evalBit query)) true).toReal) := by
  have h2 :
      (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
        GoldreichLevin.agreement (fun query => if evalBit query r_bit then r_bit else !r_bit) x) =
      1 / 2 +
        (((PMF.uniformOfFintype (BitString k)).map
          (fun query => evalBit query (x ⬝ᵥ query))) true).toReal -
        (((PMF.uniformOfFintype (BitString k)).bind fun query =>
          (PMF.uniformOfFintype Bool).map (evalBit query)) true).toReal := by
    have hguess := PRG.toReal_bind_guessOfDistinguisher
      (PMF.uniformOfFintype (BitString k)) (fun query => x ⬝ᵥ query)
      (fun query b => PMF.pure (evalBit query b))
    have hcomm :
        (((PMF.uniformOfFintype (BitString k)).bind fun query =>
          (PRG.guessOfDistinguisher (fun b => PMF.pure (evalBit query b))).map
            fun g => decide (g = (x ⬝ᵥ query))) true).toReal =
        ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          GoldreichLevin.agreement
            (fun query => if evalBit query r_bit then r_bit else !r_bit) x := by
      simp only [GoldreichLevin.agreement_eq_probability, PRG.guessOfDistinguisher,
        PMF.monad_bind_eq_bind, PMF.map, PMF.pure_bind,
        PMF.bind_bind, Function.comp_def, beq_eq_decide]
      rw [PMF.bind_comm, PMF.bind_apply_toReal]
    rw [← hcomm, hguess]
    rfl
  have hterm (r_bit : Bool) :
      (PMF.uniformOfFintype Bool r_bit).toReal *
        (2 * GoldreichLevin.agreement
          (fun query => if evalBit query r_bit then r_bit else !r_bit) x - 1) =
      2 * ((PMF.uniformOfFintype Bool r_bit).toReal *
        GoldreichLevin.agreement
          (fun query => if evalBit query r_bit then r_bit else !r_bit) x) -
      (PMF.uniformOfFintype Bool r_bit).toReal := by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, PMF.sum_toReal, h2]
  ring

private theorem uniformOfFintype_bind_bind_update_row {c2 k : ℕ} {γ : Type*}
    (idx : Fin c2) (f : (Fin c2 → BitString k) → PMF γ) :
    ((PMF.uniformOfFintype (BitString k)).bind fun query =>
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        f (Function.update rows idx query)) =
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind f :=
  PMF.uniformOfFintype_bind_bind_fst_equiv
    { toFun := fun p => (Function.update p.2 idx p.1, p.2 idx)
      invFun := fun q => (q.1 idx, Function.update q.1 idx q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp } f

private theorem cond_xor_eq (b r_bit pol : Bool) :
    ((if b then r_bit else !r_bit) ^^ pol) = (if (b ^^ pol) then r_bit else !r_bit) := by
  cases b <;> cases r_bit <;> cases pol <;> rfl

private theorem sum_mul_sum_mul_sum_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (wa : α → ℝ) (wb : β → ℝ) (wc : γ → ℝ) (f : α → β → γ → ℝ) :
    (∑ a : α, wa a * ∑ b : β, wb b * ∑ c : γ, wc c * f a b c) =
    ∑ c : γ, wc c * ∑ a : α, wa a * ∑ b : β, wb b * f a b c := by
  simp_rw [Finset.mul_sum]
  trans (∑ a : α, ∑ c : γ, ∑ b : β, wa a * (wb b * (wc c * f a b c)))
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring

/-- Single-step hybrid prediction-to-inversion inequality on the fiber of `x₀` for fixed auxiliary
words `pad`, `h1`, `z_tail`, `coins` and polarity `pol`
([Liu and Pass, Proof of Lemma 5.1, Appendix A, pp. 23–24 of arXiv:2009.11514v1][LiuPass2020]). -/
private theorem fiber_step_diff_le {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val j deg : ℕ)
    (pad h1 z_tail coins : List Bool)
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k)
    (hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k) :
    have : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    let c2 := h2Rows d γ_core k
    let m1 := l1Val d k r_val
    let m2 := l2Val d k r_val
    let idx : Fin c2 := ⟨m2 + j, hidx_lt⟩
    let h2Word (rows : Fin c2 → BitString k) :=
      List.ofFn ((blocksEquiv (m := c2) (k := k)).symm rows)
    let digestWord (rows : Fin c2 → BitString k) (x : BitString k) :=
      List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x)
    let p_succ : PMF Bool :=
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
          (evaluate (n, pad ++ h1 ++ LinearHash.wordHash m1 h1 (List.ofFn (f x₀)) ++
            h2Word rows ++ digestWord rows x.val ++ [x.val ⬝ᵥ rows idx] ++ z_tail) coins) ^^ pol
    let p_curr : PMF Bool :=
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
          (PMF.uniformOfFintype Bool).map fun b =>
            (evaluate (n, pad ++ h1 ++ LinearHash.wordHash m1 h1 (List.ofFn (f x₀)) ++
              h2Word rows ++ digestWord rows x.val ++ [b] ++ z_tail) coins) ^^ pol
    2 * ((p_succ true).toReal - (p_curr true).toReal) ≤
      1 / (GoldreichLevin.precision deg k : ℝ) +
      (if m2 = 0 then 0 else
        2 * Real.sqrt ((2 : ℝ) ^ m2 / Nat.card {x : BitString k // f x = f x₀})) +
      2 ^ (j + 1) *
        ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (((Pseudoentropy.guessInverter f
            (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
              z_tail coins (f x₀))
            (PMF.uniformOfFintype (Fin c2 → BitString k))
            (GoldreichLevin.precision deg k) (f x₀)).map (fun z => f z == f x₀)) true).toReal := by
  intro _ c2 m1 m2 idx h2Word digestWord p_succ p_curr
  let evalBit (rows : Fin c2 → BitString k) (x : BitString k) (query : BitString k) (b : Bool) :
      Bool :=
    (evaluate (n, wordChallenge k m1 (m2 + j) pad h1 (List.ofFn (f x₀))
      (h2Word rows) (digestWord rows x) [b] z_tail (List.ofFn query)) coins) ^^ pol
  have hp_succ : p_succ =
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
          (PMF.uniformOfFintype (BitString k)).map fun query =>
            evalBit rows x.val query (x.val ⬝ᵥ query) := by
    dsimp only [p_succ]
    rw [← uniformOfFintype_bind_bind_update_row idx, PMF.bind_comm]
    congr 1; funext rows
    simp only [PMF.map, Function.comp_def]
    rw [PMF.bind_comm]
    congr 1; funext x
    congr 1; funext query
    have h1_upd : h2Word (Function.update rows idx query) =
        spliceMatrixWord k (m2 + j) (h2Word rows) (List.ofFn query) :=
      (spliceMatrixWord_eq_ofFn_update rows idx query).symm
    have h2_upd : digestWord (Function.update rows idx query) x.val = digestWord rows x.val := by
      dsimp only [digestWord]
      rw [update_comp_castLE_of_eq rows idx query hlen rfl]
    have h3_upd : Function.update rows idx query idx = query := Function.update_self idx query rows
    simp only [evalBit, wordChallenge, h1_upd, h2_upd, h3_upd]
  have hp_curr : p_curr =
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
          (PMF.uniformOfFintype (BitString k)).bind fun query =>
            (PMF.uniformOfFintype Bool).map (evalBit rows x.val query) := by
    dsimp only [p_curr]
    rw [← uniformOfFintype_bind_bind_update_row idx, PMF.bind_comm]
    congr 1; funext rows
    rw [PMF.bind_comm]
    congr 1; funext x
    congr 1; funext query
    have h1_upd : h2Word (Function.update rows idx query) =
        spliceMatrixWord k (m2 + j) (h2Word rows) (List.ofFn query) :=
      (spliceMatrixWord_eq_ofFn_update rows idx query).symm
    have h2_upd : digestWord (Function.update rows idx query) x.val = digestWord rows x.val := by
      dsimp only [digestWord]
      rw [update_comp_castLE_of_eq rows idx query hlen rfl]
    simp only [evalBit, wordChallenge, h1_upd, h2_upd]
  have hpred_eq (r_bit : Bool) (rows : Fin c2 → BitString k) (x : BitString k) :
      (fun query => if evalBit rows x query r_bit then r_bit else !r_bit) =
      stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
        z_tail coins (f x₀) rows (LinearHash.hash (rows ∘ Fin.castLE hlen) x) := by
    funext query
    simp [stepPredictor, wordStepPredictor, evalBit, cond_xor_eq, m1, m2, h2Word, digestWord]
  have hdiff : 2 * ((p_succ true).toReal - (p_curr true).toReal) =
      ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
        (∑ rows : Fin c2 → BitString k,
          (PMF.uniformOfFintype (Fin c2 → BitString k) rows).toReal *
          ∑ x : {x : BitString k // f x = f x₀},
            (PMF.uniformOfFintype {x : BitString k // f x = f x₀} x).toReal *
            (2 * GoldreichLevin.agreement
              (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
                z_tail coins (f x₀) rows (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val))
              x.val - 1)) := by
    rw [hp_succ, hp_curr, PMF.bind_apply_toReal, PMF.bind_apply_toReal]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    trans (∑ rows : Fin c2 → BitString k,
      (PMF.uniformOfFintype (Fin c2 → BitString k) rows).toReal *
      ∑ x : {x : BitString k // f x = f x₀},
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀} x).toReal *
        ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (2 * GoldreichLevin.agreement
            (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
              z_tail coins (f x₀) rows (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val))
            x.val - 1))
    · refine Finset.sum_congr rfl fun rows _ => ?_
      rw [PMF.bind_apply_toReal, PMF.bind_apply_toReal]
      rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_assoc, mul_comm 2, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_sub, ← mul_assoc, mul_comm 2, mul_assoc]
      congr 1
      simp_rw [← hpred_eq _ rows x.val]
      exact (sum_bool_agreement_eq (evalBit rows x.val) x.val).symm
    · exact sum_mul_sum_mul_sum_comm _ _ _ _
  rw [hdiff]
  have hpoint (r_bit : Bool) :=
    Pseudoentropy.matrix_fiber_correlation_le f (f x₀) hlen
      (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol] z_tail coins
        (f x₀))
      (GoldreichLevin.precision deg k) (GoldreichLevin.precision_pos deg k)
  calc
    _ ≤ ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
        (1 / (GoldreichLevin.precision deg k : ℝ) +
          (if m2 = 0 then 0 else
            2 * Real.sqrt ((2 : ℝ) ^ m2 / Nat.card {x : BitString k // f x = f x₀})) +
          2 ^ (j + 1) *
            (((Pseudoentropy.guessInverter f
              (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
                z_tail coins (f x₀))
              (PMF.uniformOfFintype (Fin c2 → BitString k))
              (GoldreichLevin.precision deg k) (f x₀)).map (fun z => f z == f x₀)) true).toReal) :=
      Finset.sum_le_sum fun r_bit _ =>
        mul_le_mul_of_nonneg_left (hpoint r_bit) ENNReal.toReal_nonneg
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul,
        mul_left_comm _ ((2 : ℝ) ^ (j + 1)), ← Finset.mul_sum]

private theorem ofFn_hash_castLE_succ {k c2 w : ℕ} (rows : Fin c2 → BitString k) (x : BitString k)
    (hlen : w ≤ c2) (hidx_lt : w < c2) :
    List.ofFn (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt hidx_lt)) x) =
      List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x) ++ [x ⬝ᵥ rows ⟨w, hidx_lt⟩] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  refine congrArg₂ (· ++ ·) rfl ?_
  simp only [LinearHash.hash, Function.comp_apply, dotProduct_comm]
  rfl

private theorem uniformList_one_eq :
    BitString.uniformList 1 = (PMF.uniformOfFintype Bool).map (fun b => [b]) := by
  simpa [PMF.map, Function.comp_def] using BitString.uniformList_succ 0

private theorem uniformList_four_bind_eq {γ : Type*} (n1 n2 n3 n4 : ℕ)
    (F : List Bool → List Bool → List Bool → List Bool → PMF γ) :
    ((BitString.uniformList n1).bind fun w1 =>
      (BitString.uniformList n2).bind fun w2 =>
        (BitString.uniformList n3).bind fun w3 =>
          (BitString.uniformList n4).bind fun w4 => F w1 w2 w3 w4) =
    (PMF.uniformOfFintype (BitString n1 × BitString n2 × BitString n3 × BitString n4)).bind
      fun a => F (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) := by
  simp only [← PMF.uniformOfFintype_prod, BitString.uniformList, PMF.bind_map, PMF.bind_bind,
    Function.comp_def]

private theorem bind_map_comm_four {α β γ₁ γ₂ γ₃ δ : Type*}
    (pa : PMF α) (pb : PMF β) (p₁ : PMF γ₁) (p₂ : PMF γ₂) (p₃ : PMF γ₃)
    (f : α × β → γ₁ → γ₂ → γ₃ → δ) :
    ((pa.bind fun a => pb.map fun b => (a, b)).bind fun ab =>
      p₁.bind fun c₁ => p₂.bind fun c₂ => p₃.map fun c₃ => f ab c₁ c₂ c₃) =
    pb.bind fun b => p₁.bind fun c₁ => p₂.bind fun c₂ => p₃.bind fun c₃ =>
      pa.map fun a => f (a, b) c₁ c₂ c₃ := by
  simp only [PMF.bind_bind, Function.comp_def, PMF.map, PMF.pure_bind]
  rw [PMF.bind_comm pa pb]
  congr 1; funext b
  rw [PMF.bind_comm pa p₁]
  congr 1; funext c₁
  rw [PMF.bind_comm pa p₂]
  congr 1; funext c₂
  exact PMF.bind_comm pa p₃ (fun a c₃ => PMF.pure (f (a, b) c₁ c₂ c₃))

private theorem bind_two_comm_two {α₁ α₂ β₁ β₂ γ : Type*}
    (pa₁ : PMF α₁) (pa₂ : PMF α₂) (pb₁ : PMF β₁) (pb₂ : PMF β₂)
    (F : α₁ → α₂ → β₁ → β₂ → PMF γ) :
    (pa₁.bind fun a₁ => pa₂.bind fun a₂ => pb₁.bind fun b₁ => pb₂.bind fun b₂ =>
      F a₁ a₂ b₁ b₂) =
    (pb₁.bind fun b₁ => pb₂.bind fun b₂ => pa₁.bind fun a₁ => pa₂.bind fun a₂ =>
      F a₁ a₂ b₁ b₂) := by
  have h1 (a₁ : α₁) :
      (pa₂.bind fun a₂ => pb₁.bind fun b₁ => pb₂.bind fun b₂ => F a₁ a₂ b₁ b₂) =
      pb₁.bind fun b₁ => pb₂.bind fun b₂ => pa₂.bind fun a₂ => F a₁ a₂ b₁ b₂ := by
    rw [PMF.bind_comm pa₂ pb₁]
    congr 1; funext b₁
    exact PMF.bind_comm pa₂ pb₂ (fun a₂ b₂ => F a₁ a₂ b₁ b₂)
  simp_rw [h1]
  rw [PMF.bind_comm pa₁ pb₁]
  congr 1; funext b₁
  exact PMF.bind_comm pa₁ pb₂ (fun a₁ b₂ => pa₂.bind fun a₂ => F a₁ a₂ b₁ b₂)

private theorem le_two_mul_sum_uniformOfFintype_bool (G : Bool → ℝ) (hG : ∀ p, 0 ≤ G p)
    (pol : Bool) :
    G pol ≤ 2 * ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * G p := by
  have hpol : (PMF.uniformOfFintype Bool pol).toReal = 1 / 2 := by
    simp [PMF.uniformOfFintype_apply]
  have hle : (PMF.uniformOfFintype Bool pol).toReal * G pol ≤
      ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * G p :=
    Finset.single_le_sum (fun p _ => mul_nonneg ENNReal.toReal_nonneg (hG p)) (Finset.mem_univ pol)
  rw [hpol] at hle
  linarith

/-- Acceptance distribution of the twisted distinguisher `evaluate ... ^^ pol` at hybrid step `j`
conditioned on the fiber of `x₀`. -/
private noncomputable def fiberHybridAcceptDist {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val padLen m coinLen j : ℕ)
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k) : PMF Bool :=
  haveI : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  (BitString.uniformList padLen).bind fun pad =>
    (BitString.uniformList (k * imgLen_k)).bind fun h1 =>
      (BitString.uniformList (m - j)).bind fun z_tail =>
        (BitString.uniformList coinLen).bind fun coins =>
          (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k)).bind fun rows =>
            (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
              (evaluate (n, pad ++ h1 ++
                LinearHash.wordHash (l1Val d k r_val) h1 (List.ofFn (f x₀)) ++
                List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
                List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val) ++ z_tail) coins) ^^ pol

/-- Single-step hybrid inequality on the fiber of `x₀`, averaged over the auxiliary hybrid words
`pad`, `h1`, `z_tail`, `coins` and bounded by `stepAuxInverter`. -/
private theorem fiberHybrid_step_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg r_val n_offset j : ℕ)
    (hj : j < mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset))
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k)
    (hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k) :
    let n := coreSeedLen imgLen d γ_core k + n_offset
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen (j + 1)
          (Nat.succ_le_of_lt hidx_lt) true).toReal -
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j
          hlen true).toReal) ≤
      1 / (GoldreichLevin.precision deg k : ℝ) +
      (if l2Val d k r_val = 0 then 0 else
        2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀})) +
      2 ^ (j + 2) *
        (((ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
          k r_val n_offset j (List.ofFn (f x₀)))).map
            (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  have : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  intro n m coinLen
  let c2 := h2Rows d γ_core k
  let m1 := l1Val d k r_val
  let m2 := l2Val d k r_val
  let idx : Fin c2 := ⟨m2 + j, hidx_lt⟩
  let h2Word (rows : Fin c2 → BitString k) :=
    List.ofFn ((blocksEquiv (m := c2) (k := k)).symm rows)
  let digestWord (rows : Fin c2 → BitString k) (x : BitString k) :=
    List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x)
  let Aux := BitString n_offset × BitString (k * imgLen k) × BitString (m - (j + 1)) ×
    BitString coinLen
  let p_succ (a : Aux) : PMF Bool :=
    (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
      (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
        (evaluate (n, List.ofFn a.1 ++ List.ofFn a.2.1 ++
          LinearHash.wordHash m1 (List.ofFn a.2.1) (List.ofFn (f x₀)) ++
          h2Word rows ++ digestWord rows x.val ++ [x.val ⬝ᵥ rows idx] ++
          List.ofFn a.2.2.1) (List.ofFn a.2.2.2)) ^^ pol
  let p_curr (a : Aux) : PMF Bool :=
    (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
      (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
        (PMF.uniformOfFintype Bool).map fun b =>
          (evaluate (n, List.ofFn a.1 ++ List.ofFn a.2.1 ++
            LinearHash.wordHash m1 (List.ofFn a.2.1) (List.ofFn (f x₀)) ++
            h2Word rows ++ digestWord rows x.val ++ [b] ++
            List.ofFn a.2.2.1) (List.ofFn a.2.2.2)) ^^ pol
  have hsucc_eq :
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen (j + 1)
        (Nat.succ_le_of_lt hidx_lt) =
      (PMF.uniformOfFintype Aux).bind p_succ := by
    unfold fiberHybridAcceptDist
    rw [uniformList_four_bind_eq]
    congr 1; funext a; congr 1; funext rows; congr 1; funext x
    simp only [h2Word, digestWord, m1, m2, idx, ofFn_hash_castLE_succ rows x.val hlen hidx_lt,
      List.append_assoc]
  have hcurr_eq :
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j hlen =
      (PMF.uniformOfFintype Aux).bind p_curr := by
    have hm_sub : m - j = (m - (j + 1)) + 1 := by
      dsimp [m, n]
      omega
    have hunif_split : BitString.uniformList (m - j) =
        ((PMF.uniformOfFintype Bool).bind fun b =>
          (BitString.uniformList (m - (j + 1))).map fun z_tail => (b, z_tail)).map
            (fun bz => [bz.1] ++ bz.2) := by
      rw [hm_sub, BitString.uniformList_succ]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def]
    unfold fiberHybridAcceptDist
    rw [hunif_split]
    simp only [PMF.bind_map, Function.comp_def]
    conv_lhs =>
      arg 2; ext pad; arg 2; ext h1
      rw [bind_map_comm_four]
    rw [uniformList_four_bind_eq]
    congr 1; funext a; congr 1; funext rows; congr 1; funext x; congr 1; funext b
    simp only [h2Word, digestWord, m1, List.append_assoc, Function.comp_def]
  let invProb (a : Aux) (r_bit p : Bool) : PMF Bool :=
    (Pseudoentropy.guessInverter f
      (stepPredictor evaluate n k (imgLen k) d γ_core r_val j
        (List.ofFn a.1) (List.ofFn a.2.1) [r_bit] [p] (List.ofFn a.2.2.1) (List.ofFn a.2.2.2)
        (f x₀))
      (PMF.uniformOfFintype (Fin c2 → BitString k))
      (GoldreichLevin.precision deg k) (f x₀)).map (fun z => f z == f x₀)
  have hstep_inv :
      (ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
        k r_val n_offset j (List.ofFn (f x₀)))).map (fun w => decide (g w = List.ofFn (f x₀))) =
      (PMF.uniformOfFintype Aux).bind fun a =>
        (PMF.uniformOfFintype Bool).bind fun r_bit =>
          (PMF.uniformOfFintype Bool).bind fun p => invProb a r_bit p := by
    have hmap_inner (pad h1 r_word pol_word z_tail coins : List Bool) :
        (ProbComp.eval (innerGuessInverter g evaluate d γ_core deg n k r_val j
          pad h1 (List.ofFn (f x₀)) r_word pol_word z_tail coins)).map
            (fun w => decide (g w = List.ofFn (f x₀))) =
        (Pseudoentropy.guessInverter f
          (stepPredictor evaluate n k (imgLen k) d γ_core r_val j
            pad h1 r_word pol_word z_tail coins (f x₀))
          (PMF.uniformOfFintype (Fin c2 → BitString k))
          (GoldreichLevin.precision deg k) (f x₀)).map (fun z => f z == f x₀) := by
      rw [eval_innerGuessInverter g f hf, PMF.map_comp]
      congr 1; funext z
      simp [hf z, List.ofFn_inj, beq_eq_decide]
    dsimp only [n] at hmap_inner
    simp only [stepAuxInverter, ProbComp.eval_bind, BitString.eval_sampleList, PMF.map_bind]
    simp_rw [hmap_inner]
    conv_lhs =>
      arg 2; ext pad; arg 2; ext h1
      rw [bind_two_comm_two (BitString.uniformList 1) (BitString.uniformList 1)
        (BitString.uniformList (m - (j + 1))) (BitString.uniformList coinLen)]
    rw [uniformList_four_bind_eq]
    congr 1; funext a
    simp only [uniformList_one_eq, PMF.bind_map, Function.comp_def, invProb, n]
  have hpoint (a : Aux) :
      2 * ((p_succ a true).toReal - (p_curr a true).toReal) ≤
        1 / (GoldreichLevin.precision deg k : ℝ) +
        (if m2 = 0 then 0 else
          2 * Real.sqrt ((2 : ℝ) ^ m2 / Nat.card {x : BitString k // f x = f x₀})) +
        2 ^ (j + 2) *
          (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
            ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
              (invProb a r_bit p true).toReal) := by
    have hfib : 2 * ((p_succ a true).toReal - (p_curr a true).toReal) ≤
        1 / (GoldreichLevin.precision deg k : ℝ) +
        (if m2 = 0 then 0 else
          2 * Real.sqrt ((2 : ℝ) ^ m2 / Nat.card {x : BitString k // f x = f x₀})) +
        2 ^ (j + 1) *
          (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
            (invProb a r_bit pol true).toReal) :=
      fiber_step_diff_le f x₀ evaluate pol n d γ_core r_val j deg
        (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) hlen hidx_lt
    have hpol_le (r_bit : Bool) :
        (invProb a r_bit pol true).toReal ≤
          2 * ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
            (invProb a r_bit p true).toReal :=
      le_two_mul_sum_uniformOfFintype_bool (fun p => (invProb a r_bit p true).toReal)
        (fun _ => ENNReal.toReal_nonneg) pol
    have hsum_le :
        (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (invProb a r_bit pol true).toReal) ≤
        2 * ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * (invProb a r_bit p true).toReal := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r_bit _ => ?_
      linarith [mul_le_mul_of_nonneg_left (hpol_le r_bit)
        (ENNReal.toReal_nonneg : 0 ≤ (PMF.uniformOfFintype Bool r_bit).toReal)]
    have hmul : (2 : ℝ) ^ (j + 1) *
        (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (invProb a r_bit pol true).toReal) ≤
        2 ^ (j + 2) *
          (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
            ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
              (invProb a r_bit p true).toReal) := by
      calc
        _ ≤ (2 : ℝ) ^ (j + 1) * (2 * ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
              ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
                (invProb a r_bit p true).toReal) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = 2 ^ (j + 2) * ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
              ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
                (invProb a r_bit p true).toReal := by ring
    linarith
  rw [hsucc_eq, hcurr_eq, hstep_inv]
  simp only [PMF.bind_apply_toReal]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  have h_lhs :
      (∑ a : Aux, 2 * ((PMF.uniformOfFintype Aux a).toReal * (p_succ a true).toReal -
        (PMF.uniformOfFintype Aux a).toReal * (p_curr a true).toReal)) =
      ∑ a : Aux, (PMF.uniformOfFintype Aux a).toReal *
        (2 * ((p_succ a true).toReal - (p_curr a true).toReal)) :=
    Finset.sum_congr rfl fun a _ => by ring
  rw [h_lhs]
  calc
    _ ≤ ∑ a : Aux, (PMF.uniformOfFintype Aux a).toReal *
        (1 / (GoldreichLevin.precision deg k : ℝ) +
          (if m2 = 0 then 0 else
            2 * Real.sqrt ((2 : ℝ) ^ m2 / Nat.card {x : BitString k // f x = f x₀})) +
          2 ^ (j + 2) *
            (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
              ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal *
                (invProb a r_bit p true).toReal)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint a) ENNReal.toReal_nonneg
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul,
        mul_left_comm _ ((2 : ℝ) ^ (j + 2)), ← Finset.mul_sum, m2]

private theorem single_le_mul_sampleDyadicIndex {α : Type} (bound i : ℕ) (hi : i ≤ bound)
    (P : ℕ → ProbComp α) (E : α → Bool) :
    (((ProbComp.eval (P i)).map E) true).toReal ≤
      (dyadicSize bound : ℝ) *
        (((ProbComp.eval (do let j ← ProbComp.sampleDyadicIndex bound; P j)).map E)
          true).toReal := by
  have hi_lt : i < dyadicSize bound := lt_of_le_of_lt hi (lt_dyadicSize bound)
  let idx : Fin (dyadicSize bound) := ⟨i, hi_lt⟩
  have hpos : (0 : ℝ) < dyadicSize bound := Nat.cast_pos.mpr (dyadicSize_pos bound)
  simp only [ProbComp.eval_bind, ProbComp.eval_sampleDyadicIndex, PMF.bind_map, PMF.map_bind,
    Function.comp_def, PMF.bind_apply_toReal]
  have hle := Finset.single_le_sum
    (f := fun j : Fin (dyadicSize bound) =>
      (PMF.uniformOfFintype (Fin (dyadicSize bound)) j).toReal *
        (((ProbComp.eval (P j.val)).map E) true).toReal)
    (fun j _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (Finset.mem_univ idx)
  have hunif : (PMF.uniformOfFintype (Fin (dyadicSize bound)) idx).toReal =
      (dyadicSize bound : ℝ)⁻¹ := by
    simp [PMF.uniformOfFintype_apply]
  rw [hunif] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul

private theorem sum_range_le_mul_sampleDyadicIndex {α : Type} (bound : ℕ)
    (P : ℕ → ProbComp α) (E : α → Bool) :
    ∑ j ∈ Finset.range bound, (((ProbComp.eval (P j)).map E) true).toReal ≤
      (dyadicSize bound : ℝ) *
        (((ProbComp.eval (do let j ← ProbComp.sampleDyadicIndex bound; P j)).map E)
          true).toReal := by
  have hle : bound ≤ dyadicSize bound := (lt_dyadicSize bound).le
  have hpos : (0 : ℝ) < dyadicSize bound := Nat.cast_pos.mpr (dyadicSize_pos bound)
  simp only [ProbComp.eval_bind, ProbComp.eval_sampleDyadicIndex, PMF.bind_map, PMF.map_bind,
    Function.comp_def, PMF.bind_apply_toReal]
  have hsum_eq :
      (∑ j : Fin (dyadicSize bound),
        (PMF.uniformOfFintype (Fin (dyadicSize bound)) j).toReal *
          (((ProbComp.eval (P j.val)).map E) true).toReal) =
      (dyadicSize bound : ℝ)⁻¹ *
        ∑ j ∈ Finset.range (dyadicSize bound),
          (((ProbComp.eval (P j)).map E) true).toReal := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (((ProbComp.eval (P j)).map E) true).toReal),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [PMF.uniformOfFintype_apply]
  rw [hsum_eq, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
    (fun _ _ _ => ENNReal.toReal_nonneg)

/-- Telescoped hybrid inequality across all `m = mActual d γ k n` steps on the fiber of `x₀`,
bounded by `condInverter`. -/
private theorem fiberHybrid_total_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg r_val n_offset : ℕ)
    (hr_le : r_val ≤ k + 1)
    (hn_off_le : n_offset ≤ coreSeedLen imgLen d γ_core (k + 1))
    (hm_le : l2Val d k r_val + mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) ≤
      h2Rows d γ_core k) :
    let n := coreSeedLen imgLen d γ_core k + n_offset
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen m
          hm_le true).toReal -
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen 0
          (by omega) true).toReal) ≤
      (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        (if l2Val d k r_val = 0 then 0 else
          2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀}))) +
      (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) *
        (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
          k (List.ofFn (f x₀)))).map
            (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  intro n m coinLen
  let F (j : ℕ) : ℝ :=
    if hj : l2Val d k r_val + j ≤ h2Rows d γ_core k then
      (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j hj true).toReal
    else 0
  have hF_m : F m =
      (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen m
        hm_le true).toReal := dite_eq_left hm_le
  have hF_0 : F 0 =
      (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen 0
        (by omega) true).toReal := dite_eq_left (by omega)
  have htel : 2 * (F m - F 0) = ∑ j ∈ Finset.range m, 2 * (F (j + 1) - F j) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub]
  let C : ℝ := 1 / (GoldreichLevin.precision deg k : ℝ) +
    (if l2Val d k r_val = 0 then 0 else
      2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀}))
  let stepInv (j : ℕ) : ℝ :=
    (((ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
      k r_val n_offset j (List.ofFn (f x₀)))).map
        (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal
  have hstep (j : ℕ) (hj : j ∈ Finset.range m) :
      2 * (F (j + 1) - F j) ≤ C + (2 : ℝ) ^ (m + 1) * stepInv j := by
    have hj_lt : j < m := Finset.mem_range.mp hj
    have hj_lt' : j < mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) := hj_lt
    have hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k := by omega
    have hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k := hidx_lt.le
    have hlen_succ : l2Val d k r_val + (j + 1) ≤ h2Rows d γ_core k := Nat.succ_le_of_lt hidx_lt
    have hFj1 : F (j + 1) =
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen (j + 1)
          hlen_succ true).toReal := dite_eq_left hlen_succ
    have hFj : F j =
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j
          hlen true).toReal := dite_eq_left hlen
    rw [hFj1, hFj]
    have h1 := fiberHybrid_step_le g imgLen f hf x₀ evaluate pol d γ_core γ c_eval d_eval deg
      r_val n_offset j hj_lt' hlen hidx_lt
    have hpow : (2 : ℝ) ^ (j + 2) ≤ (2 : ℝ) ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul : (2 : ℝ) ^ (j + 2) * stepInv j ≤ (2 : ℝ) ^ (m + 1) * stepInv j :=
      mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg
    dsimp only [C, stepInv] at h1 ⊢
    linarith
  have hsum_step : 2 * (F m - F 0) ≤
      (m : ℝ) * C + (2 : ℝ) ^ (m + 1) * ∑ j ∈ Finset.range m, stepInv j := by
    rw [htel]
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hdyadic_j := sum_range_le_mul_sampleDyadicIndex m
    (fun j => stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_offset j
      (List.ofFn (f x₀)))
    (fun w => decide (g w = List.ofFn (f x₀)))
  have hdyadic_n := single_le_mul_sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
    n_offset hn_off_le
    (fun n_off => do
      let j ← ProbComp.sampleDyadicIndex
        (mActual d γ k (coreSeedLen imgLen d γ_core k + n_off))
      stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_off j
        (List.ofFn (f x₀)))
    (fun w => decide (g w = List.ofFn (f x₀)))
  have hdyadic_r := single_le_mul_sampleDyadicIndex (k + 1) r_val hr_le
    (fun r_v => do
      let n_off ← ProbComp.sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
      let j ← ProbComp.sampleDyadicIndex
        (mActual d γ k (coreSeedLen imgLen d γ_core k + n_off))
      stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_v n_off j
        (List.ofFn (f x₀)))
    (fun w => decide (g w = List.ofFn (f x₀)))
  have hinv_chain :
      ∑ j ∈ Finset.range m, stepInv j ≤
        (dyadicSize m : ℝ) * (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
          (dyadicSize (k + 1) : ℝ) *
          (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
            k (List.ofFn (f x₀)))).map
              (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
    calc
      ∑ j ∈ Finset.range m, stepInv j
        ≤ (dyadicSize m : ℝ) *
            (((ProbComp.eval (do
              let j ← ProbComp.sampleDyadicIndex m
              stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_offset j
                (List.ofFn (f x₀)))).map
                  (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := hdyadic_j
      _ ≤ (dyadicSize m : ℝ) *
            ((dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
              (((ProbComp.eval (do
                let n_off ← ProbComp.sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
                let j ← ProbComp.sampleDyadicIndex
                  (mActual d γ k (coreSeedLen imgLen d γ_core k + n_off))
                stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_off j
                  (List.ofFn (f x₀)))).map
                    (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal) :=
        mul_le_mul_of_nonneg_left hdyadic_n (by positivity)
      _ ≤ (dyadicSize m : ℝ) *
            ((dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
              ((dyadicSize (k + 1) : ℝ) *
                (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
                  k (List.ofFn (f x₀)))).map
                    (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdyadic_r (by positivity)) (by positivity)
      _ = _ := by ring
  rw [← hF_m, ← hF_0]
  have hmul_inv :=
    mul_le_mul_of_nonneg_left hinv_chain (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1))
  dsimp only [C] at hsum_step
  linarith

private theorem inversionGame_succProbability_eq (g : List Bool → List Bool) {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (adversary : Inverter) :
    (Game.succProbability (ProbComp.eval (inversionGame g adversary k)) : ℝ) =
      ∑ x₀ : BitString k, (PMF.uniformOfFintype (BitString k) x₀).toReal *
        (((ProbComp.eval (adversary k (List.ofFn (f x₀)))).map
          (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  rw [Game.coe_succProbability]
  simp only [inversionGame, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
    BitString.uniformList, PMF.bind_map, Function.comp_def, PMF.bind_apply_toReal, beq_eq_decide]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  rw [hf x₀]
  rfl

/-- Telescoped hybrid inequality averaged over a dense regularity bucket $S_{k, r}$ under the
regularity gap $r + d \lfloor \log_2 k \rfloor \le k$. -/
private theorem bucketHybrid_total_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (r : Fin (k + 1)) (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg n_offset n : ℕ)
    (hn_eq : coreSeedLen imgLen d γ_core k + n_offset = n)
    (hgap : r.val + d * Nat.log 2 k ≤ k)
    (hn_off_le : n_offset ≤ coreSeedLen imgLen d γ_core (k + 1))
    (hm_le : l2Val d k r.val + mActual d γ k n ≤ h2Rows d γ_core k) :
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    let side := PMF.uniformOfFinset (regularityBucket f r) hS
    2 * (((side.bind fun x₀ =>
          fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m
            hm_le) true).toReal -
        ((side.bind fun x₀ =>
          fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
            (by omega)) true).toReal) ≤
      (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) +
      (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
        (Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) := by
  subst hn_eq
  intro m coinLen side
  let n := coreSeedLen imgLen d γ_core k + n_offset
  have hr_le : r.val ≤ k + 1 := r.isLt.le
  let invX (x₀ : BitString k) : ℝ :=
    (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
      k (List.ofFn (f x₀)))).map
        (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal
  let W : ℝ := (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
    (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) * (dyadicSize (k + 1) : ℝ)
  have hpoint (x₀ : BitString k) :
      (side x₀).toReal *
        (2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m
              hm_le true).toReal -
            (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
              (by omega) true).toReal)) ≤
      (side x₀).toReal *
        ((m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
          2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) + W * invX x₀) := by
    by_cases hx₀ : x₀ ∈ regularityBucket f r
    · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have htot := fiberHybrid_total_le g imgLen f hf x₀ evaluate pol d γ_core γ c_eval d_eval deg
        r.val n_offset hr_le hn_off_le hm_le
      have hfib_err :
          (if l2Val d k r.val = 0 then 0 else
            2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r.val) /
              Nat.card {x : BitString k // f x = f x₀})) ≤
          2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
        split_ifs with hm2
        · positivity
        · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
          have hl2 := l2Val_eq_of_gap hgap
          have hr_split : l2Val d k r.val + d * Nat.log 2 k = r.val := by omega
          have hcard : (2 : ℝ) ^ r.val ≤ Nat.card {x : BitString k // f x = f x₀} := by
            exact_mod_cast (card_fiber_of_mem_regularityBucket f r hx₀).1
          have hpow : (2 : ℝ) ^ r.val =
              (2 : ℝ) ^ (l2Val d k r.val) * (2 : ℝ) ^ (d * Nat.log 2 k) := by
            rw [← pow_add, hr_split]
          calc
            (2 : ℝ) ^ (l2Val d k r.val) / Nat.card {x : BitString k // f x = f x₀}
              ≤ (2 : ℝ) ^ (l2Val d k r.val) / (2 : ℝ) ^ r.val :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hcard
            _ = 1 / (2 : ℝ) ^ (d * Nat.log 2 k) := by
                rw [hpow, div_mul_eq_div_div, div_self (by positivity)]
      have hm_err := mul_le_mul_of_nonneg_left
        (add_le_add_left hfib_err (1 / (GoldreichLevin.precision deg k : ℝ)))
        (by positivity : (0 : ℝ) ≤ m)
      dsimp only [W, invX, m, n, coinLen] at htot ⊢
      linarith
    · have h0 : side x₀ = 0 := by simp [side, PMF.uniformOfFinset_apply, hx₀]
      simp [h0]
  simp only [PMF.bind_apply_toReal]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  have h_lhs :
      (∑ x₀ : BitString k, 2 * ((side x₀).toReal *
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m
          hm_le true).toReal -
        (side x₀).toReal *
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
          (by omega) true).toReal)) =
      ∑ x₀ : BitString k, (side x₀).toReal *
        (2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m
              hm_le true).toReal -
            (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
              (by omega) true).toReal)) :=
    Finset.sum_congr rfl fun x₀ _ => by ring
  rw [h_lhs]
  have hsum1 := Finset.sum_le_sum fun x₀ (_ : x₀ ∈ Finset.univ) => hpoint x₀
  have hsum2 :
      (∑ x₀ : BitString k, (side x₀).toReal *
        ((m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
          2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) + W * invX x₀)) =
      (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) +
      W * ∑ x₀ : BitString k, (side x₀).toReal * invX x₀ := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul,
      mul_left_comm _ W, ← Finset.mul_sum]
  have hbucket_le := sum_uniformOfFinset_le_mul_uniformOfFintype (regularityBucket f r) hS hdense
    invX (fun _ => ENNReal.toReal_nonneg)
  have hinv_eq := inversionGame_succProbability_eq g f hf
    (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg)
  rw [← hinv_eq] at hbucket_le
  have hW_nonneg : 0 ≤ W := by dsimp [W]; positivity
  have hmul_W := mul_le_mul_of_nonneg_left hbucket_le hW_nonneg
  dsimp only [W, side] at hsum1 hsum2 hmul_W ⊢
  linarith

private theorem bind_three_comm_fourth {α₁ α₂ α₃ α₄ β : Type*}
    (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄)
    (F : α₁ → α₂ → α₃ → α₄ → β) :
    (p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ => p₄.map fun a₄ => F a₁ a₂ a₃ a₄) =
    (p₄.bind fun a₄ => p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.map fun a₃ => F a₁ a₂ a₃ a₄) := by
  rw [PMF.bind_comm p₄ p₁]
  congr 1; funext a₁
  rw [PMF.bind_comm p₄ p₂]
  congr 1; funext a₂
  exact PMF.bind_comm p₃ p₄ (fun a₃ a₄ => PMF.pure (F a₁ a₂ a₃ a₄))

private theorem bind_five_comm_sixth {α₁ α₂ α₃ α₄ α₅ α₆ β : Type*}
    (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄) (p₅ : PMF α₅) (p₆ : PMF α₆)
    (F : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → β) :
    (p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ => p₄.bind fun a₄ =>
      p₅.bind fun a₅ => p₆.map fun a₆ => F a₁ a₂ a₃ a₄ a₅ a₆) =
    (p₆.bind fun a₆ => p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ =>
      p₄.bind fun a₄ => p₅.map fun a₅ => F a₁ a₂ a₃ a₄ a₅ a₆) := by
  have h (a₁ : α₁) := bind_four_comm_fifth p₂ p₃ p₄ p₅ p₆ (F a₁)
  simp_rw [h]
  exact PMF.bind_comm p₁ p₆ _

private theorem bind_comm_five_inner_map {α₀ α₁ α₂ α₃ α₄ α₅ β γ : Type*} {α₆ : α₀ → Type*}
    (p₀ : PMF α₀) (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄) (p₅ : PMF α₅)
    (q : ∀ a₀, PMF (α₆ a₀)) (v : ∀ a₀, α₆ a₀ → β)
    (H : α₁ → α₂ → α₃ → α₄ → α₅ → β → γ) :
    (p₀.bind fun a₀ => p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ =>
      p₄.bind fun a₄ => p₅.bind fun a₅ => (q a₀).map fun a₆ => H a₁ a₂ a₃ a₄ a₅ (v a₀ a₆)) =
    (p₀.bind fun a₀ => (q a₀).map (v a₀)).bind fun b =>
      p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ =>
        p₄.bind fun a₄ => p₅.map fun a₅ => H a₁ a₂ a₃ a₄ a₅ b := by
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hinner (a₀ : α₀) :=
    bind_five_comm_sixth p₁ p₂ p₃ p₄ p₅ (q a₀)
      (fun a₁ a₂ a₃ a₄ a₅ a₆ => H a₁ a₂ a₃ a₄ a₅ (v a₀ a₆))
  simp_rw [hinner]

/-- Averaging `fiberHybridAcceptDist` over $x_0 \leftarrow S_{k, r}$ collapses the fiber resampling
and replaces the row-indexed matrix by a flat `BitString (h2Rows * k)` seed. -/
private theorem bind_fiberHybridAcceptDist_eq {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core padLen m coinLen j : ℕ)
    (hlen : l2Val d k r.val + j ≤ h2Rows d γ_core k) :
    ((PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val padLen m coinLen j hlen) =
    (PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x =>
      (BitString.uniformList padLen).bind fun pad =>
        (BitString.uniformList (k * imgLen_k)).bind fun h1 =>
          (BitString.uniformList (m - j)).bind fun z_tail =>
            (BitString.uniformList coinLen).bind fun coins =>
              (PMF.uniformOfFintype (BitString (h2Rows d γ_core k * k))).map fun h2 =>
                (evaluate (n, pad ++ h1 ++
                  LinearHash.wordHash (l1Val d k r.val) h1 (List.ofFn (f x)) ++
                  List.ofFn h2 ++
                  List.ofFn (LinearHash.hash (block h2 ∘ Fin.castLE hlen) x) ++
                  z_tail) coins) ^^ pol := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  have hrows_eq :
      PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k) =
        (PMF.uniformOfFintype (BitString (h2Rows d γ_core k * k))).map
          (blocksEquiv (m := h2Rows d γ_core k) (k := k)) :=
    (PMF.uniformOfFintype_map_equiv (blocksEquiv (m := h2Rows d γ_core k) (k := k))).symm
  have hinner (x₀ : BitString k) (pad h1 z_tail coins : List Bool)
      (rows : Fin (h2Rows d γ_core k) → BitString k) :
      ((PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
        (evaluate (n, pad ++ h1 ++
          LinearHash.wordHash (l1Val d k r.val) h1 (List.ofFn (f x₀)) ++
          List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
          List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val) ++
          z_tail) coins) ^^ pol) =
      (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
        (evaluate (n, pad ++ h1 ++
          LinearHash.wordHash (l1Val d k r.val) h1 (List.ofFn (f x.val)) ++
          List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
          List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val) ++
          z_tail) coins) ^^ pol := by
    congr 1; funext x; rw [x.property]
  unfold fiberHybridAcceptDist
  simp_rw [hinner]
  rw [bind_comm_five_inner_map (PMF.uniformOfFinset (regularityBucket f r) hS)
    (BitString.uniformList padLen) (BitString.uniformList (k * imgLen_k))
    (BitString.uniformList (m - j)) (BitString.uniformList coinLen)
    (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k))
    (fun x₀ => PMF.uniformOfFintype {x : BitString k // f x = f x₀})
    (fun _ x => x.val)
    (fun pad h1 z_tail coins rows x =>
      (evaluate (n, pad ++ h1 ++
        LinearHash.wordHash (l1Val d k r.val) h1 (List.ofFn (f x)) ++
        List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
        List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x) ++
        z_tail) coins) ^^ pol)]
  rw [bind_regularityBucket_fiber_eq f r hS]
  congr 1; funext x; congr 1; funext pad; congr 1; funext h1; congr 1; funext z_tail
  congr 1; funext coins
  rw [hrows_eq, PMF.map_comp]
  congr 1; funext h2
  dsimp only [Function.comp_def]
  rw [Equiv.symm_apply_apply]
  rfl

/-- Extend a core LHL tuple `(h1, d1, h2, d2)` with random `pad`, `z_tail`, and `coins` and
evaluate the twisted distinguisher. -/
private noncomputable def evalCore {k imgLen_k m1 m2 c2 : ℕ}
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n padLen m coinLen : ℕ)
    (c : (BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :
    PMF Bool :=
  (BitString.uniformList padLen).bind fun pad =>
    (BitString.uniformList m).bind fun z_tail =>
      (BitString.uniformList coinLen).map fun coins =>
        (evaluate (n, pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
          List.ofFn c.2.1 ++ List.ofFn c.2.2 ++ z_tail) coins) ^^ pol

/-- At hybrid step `j = 0`, averaging `fiberHybridAcceptDist` over $S_{k, r}$ equals
`coreLHLDist` bound to `evalCore`. -/
private theorem bind_fiberHybridAcceptDist_zero_eq {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core padLen m coinLen : ℕ)
    (hlen0 : l2Val d k r.val + 0 ≤ h2Rows d γ_core k) :
    ((PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val padLen m coinLen 0 hlen0) =
    (coreLHLDist f r hS (l1Val_le d k r.val) (l2Val_le_h2Rows d γ_core k r.val)).bind
      (evalCore evaluate pol n padLen m coinLen) := by
  rw [bind_fiberHybridAcceptDist_eq]
  unfold coreLHLDist evalCore
  simp only [Nat.sub_zero, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1; funext x
  have h1_eq : BitString.uniformList (k * imgLen_k) =
      (PMF.uniformOfFintype (BitString (k * imgLen_k))).map List.ofFn := rfl
  rw [PMF.bind_comm (BitString.uniformList padLen)]
  rw [h1_eq, PMF.bind_map]
  congr 1; funext h1
  dsimp only [Function.comp_def]
  rw [bind_three_comm_fourth]
  congr 1; funext h2; congr 1; funext pad; congr 1; funext z_tail; congr 1; funext coins
  have hw := wordHash_ofFn_prefix (l1Val_le d k r.val) h1 (f x)
  simp only [Function.comp_def] at hw ⊢
  rw [hw]
  rfl

private theorem bind_four_comm_fifth_bind {α₁ α₂ α₃ α₄ α₅ β : Type*}
    (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄) (p₅ : PMF α₅)
    (F : α₁ → α₂ → α₃ → α₄ → α₅ → PMF β) :
    (p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ => p₄.bind fun a₄ =>
      p₅.bind fun a₅ => F a₁ a₂ a₃ a₄ a₅) =
    (p₅.bind fun a₅ => p₁.bind fun a₁ => p₂.bind fun a₂ => p₃.bind fun a₃ =>
      p₄.bind fun a₄ => F a₁ a₂ a₃ a₄ a₅) := by
  rw [PMF.bind_comm p₅ p₁]
  congr 1; funext a₁
  rw [PMF.bind_comm p₅ p₂]
  congr 1; funext a₂
  rw [PMF.bind_comm p₅ p₃]
  congr 1; funext a₃
  exact PMF.bind_comm p₄ p₅ (fun a₄ a₅ => F a₁ a₂ a₃ a₄ a₅)

/-- Binding `unifCoreDist` to `evalCore` yields the ideal uniform challenge distribution of length
`L = padLen + k * imgLen_k + m1 + c2 * k + m2 + m`. -/
private theorem unifCoreDist_bind_evalCore_eq (k imgLen_k m1 m2 c2 : ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n padLen m coinLen L : ℕ)
    (hL : padLen + k * imgLen_k + m1 + c2 * k + m2 + m = L) :
    (unifCoreDist k imgLen_k m1 m2 c2).bind (evalCore evaluate pol n padLen m coinLen) =
      (BitString.uniformList L).bind fun y =>
        (BitString.uniformList coinLen).map fun coins => (evaluate (n, y) coins) ^^ pol := by
  have hpad : BitString.uniformList padLen =
      (PMF.uniformOfFintype (BitString padLen)).map List.ofFn := rfl
  have hstep1 :
      (unifCoreDist k imgLen_k m1 m2 c2).bind (evalCore evaluate pol n padLen m coinLen) =
      ((PMF.uniformOfFintype (BitString padLen)).bind fun pad =>
        (PMF.uniformOfFintype (BitString (k * imgLen_k))).bind fun h1 =>
          (PMF.uniformOfFintype (BitString m1)).bind fun d1 =>
            (PMF.uniformOfFintype (BitString (c2 * k))).bind fun h2 =>
              (PMF.uniformOfFintype (BitString m2)).map fun d2 =>
                List.ofFn pad ++ List.ofFn h1 ++ List.ofFn d1 ++
                  List.ofFn h2 ++ List.ofFn d2).bind fun prefix_word =>
        (BitString.uniformList m).bind fun z_tail =>
          (BitString.uniformList coinLen).map fun coins =>
            (evaluate (n, prefix_word ++ z_tail) coins) ^^ pol := by
    unfold unifCoreDist evalCore
    rw [hpad]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    exact bind_four_comm_fifth_bind _ _ _ _ _ _
  rw [hstep1, uniformOfFintype_five_append]
  have hadd :
      ((BitString.uniformList (padLen + k * imgLen_k + m1 + c2 * k + m2)).bind fun prefix_word =>
        (BitString.uniformList m).map fun z_tail => prefix_word ++ z_tail) =
      BitString.uniformList L := by
    rw [← hL, ← BitString.uniformList_add]
  have hbind :
      ((BitString.uniformList (padLen + k * imgLen_k + m1 + c2 * k + m2)).bind fun prefix_word =>
        (BitString.uniformList m).bind fun z_tail =>
          (BitString.uniformList coinLen).map fun coins =>
            (evaluate (n, prefix_word ++ z_tail) coins) ^^ pol) =
      ((BitString.uniformList (padLen + k * imgLen_k + m1 + c2 * k + m2)).bind fun prefix_word =>
        (BitString.uniformList m).map fun z_tail => prefix_word ++ z_tail).bind fun y =>
          (BitString.uniformList coinLen).map fun coins =>
            (evaluate (n, y) coins) ^^ pol := by
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [hbind, hadd]

private theorem bind_map_comm {α β γ : Type*} (pa : PMF α) (pb : PMF β) (f : α → β → γ) :
    (pa.bind fun a => pb.map fun b => f a b) =
    (pb.bind fun b => pa.map fun a => f a b) := by
  simp only [PMF.map]
  exact PMF.bind_comm pa pb (fun a b => PMF.pure (f a b))

private theorem bind_top_four_eq {α₀ α₁ α₂ α₃ α₄ β : Type*}
    (p₀ : PMF α₀) (p₁ : PMF α₁) (p₂ : PMF α₂) (p₃ : PMF α₃) (p₄ : PMF α₄)
    (v₁ : α₁ → List Bool) (v₂ : α₂ → List Bool)
    (u₁ u₂ z₀ : PMF (List Bool))
    (hu₁ : u₁ = p₁.map v₁) (hu₂ : u₂ = p₂.map v₂) (hz₀ : z₀ = PMF.pure [])
    (F₁ : α₀ → List Bool → List Bool → List Bool → α₄ → α₃ → β)
    (v_seed : α₀ → α₂ → α₃ → α₁ → List Bool)
    (F₂ : List Bool → α₄ → β)
    (hF : ∀ a₀ a₁ a₂ a₃ a₄,
      F₁ a₀ (v₁ a₁) (v₂ a₂) [] a₄ a₃ = F₂ (v_seed a₀ a₂ a₃ a₁) a₄) :
    (p₀.bind fun a₀ => u₁.bind fun w₁ => u₂.bind fun w₂ =>
      z₀.bind fun w₃ => p₄.bind fun a₄ => p₃.map fun a₃ => F₁ a₀ w₁ w₂ w₃ a₄ a₃) =
    (p₀.bind fun a₀ => p₂.bind fun a₂ => p₃.bind fun a₃ => p₁.map fun a₁ =>
      v_seed a₀ a₂ a₃ a₁).bind (fun seed => p₄.map fun a₄ => F₂ seed a₄) := by
  subst hu₁; subst hu₂; subst hz₀
  simp only [PMF.pure_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def]
  congr 1; funext a₀
  rw [PMF.bind_comm p₁ p₂]
  congr 1; funext a₂
  have hinner (a₁ : α₁) :
      (p₄.bind fun a₄ => p₃.map fun a₃ => F₁ a₀ (v₁ a₁) (v₂ a₂) [] a₄ a₃) =
      p₃.bind fun a₃ => p₄.map fun a₄ => F₁ a₀ (v₁ a₁) (v₂ a₂) [] a₄ a₃ :=
    bind_map_comm p₄ p₃ _
  simp_rw [hinner]
  rw [PMF.bind_comm p₁ p₃]
  congr 1; funext a₃; congr 1; funext a₁; congr 1; funext a₄
  exact hF a₀ a₁ a₂ a₃ a₄

/-- At hybrid step `j = mActual d γ k n`, averaging `fiberHybridAcceptDist` over $S_{k, r(k)}$
equals the real conditional generator output distribution on `condSeedSet` fed into the twisted
distinguisher. -/
private theorem bind_fiberHybridAcceptDist_top_eq (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ : ℕ) (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1))
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    {n coinLen : ℕ}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n)
    (hk_2d : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hf : ∀ x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n),
      g (List.ofFn x) =
        List.ofFn (ofList (imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
          (g (List.ofFn x))))
    (hS_eq : S (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =
      regularityBucket
        (fun x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =>
          ofList (imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
            (g (List.ofFn x)))
        (r (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)))
    (hm_le :
      let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
      l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
    let hS_reg : (regularityBucket f (r k)).Nonempty := hS_eq ▸ hS k
    ((PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val
        (n - coreSeedLen imgLen d γ_core k) (mActual d γ k n) coinLen (mActual d γ k n) hm_le) =
    ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).bind fun seed =>
        (BitString.uniformList coinLen).map fun coins =>
          (evaluate (n, fullGen g imgLen d γ_core γ seed) coins) ^^ pol := by
  intro k f hS_reg
  rw [bind_fiberHybridAcceptDist_eq]
  have hcond_seed := uniformOfFinset_condSeedSet_map_ofFn imgLen d γ_core S hS r hfits
  dsimp only at hcond_seed
  have hS_pmf : PMF.uniformOfFinset (S k) (hS k) =
      PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg := by
    congr 1
  rw [hcond_seed, hS_pmf]
  refine bind_top_four_eq _ _ _ _ _ List.ofFn List.ofFn _ _ _ rfl rfl (by simp) _ _ _
    fun x pad h1 h2 coins => ?_
  have hplen : (packSeedWords (r k).val (x, h1, h2, pad)).length = n :=
    length_packSeedWords (Nat.le_of_lt_succ (r k).isLt) hfits (x, h1, h2, pad)
  have hfits_z : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
        (packSeedWords (r k).val (x, h1, h2, pad)).length) ≤
      (packSeedWords (r k).val (x, h1, h2, pad)).length := by
    rw [hplen]; exact hfits
  have hk_z : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
        (packSeedWords (r k).val (x, h1, h2, pad)).length)) ≤
      GeneratorReindex.parameter (coreSeedLen imgLen d γ_core)
        (packSeedWords (r k).val (x, h1, h2, pad)).length := by
    rw [hplen]; exact hk_2d
  rw [List.append_nil, fullGen_eq_rawGen hfits_z hk_z,
    rawGen_packSeedWords g imgLen d γ_core γ n (r k).val
      (Nat.le_of_lt_succ (r k).isLt) hfits (x, h1, h2, pad),
    hf x, wordHash_ofFn_prefix hm_le h2 x]

private theorem two_pow_mul_log_le_pow (A : ℕ) {k : ℕ} (hk : 0 < k) :
    2 ^ (A * Nat.log 2 k) ≤ k ^ A := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hk.ne') A

private theorem pow_le_two_pow_two_mul_log (B : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    k ^ B ≤ 2 ^ (2 * B * Nat.log 2 k) := by
  have hlog : 1 ≤ Nat.log 2 k := Nat.le_log_of_pow_le Nat.one_lt_two hk
  have hk_le : k ≤ 2 ^ (2 * Nat.log 2 k) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two k).le.trans
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  calc
    k ^ B ≤ (2 ^ (2 * Nat.log 2 k)) ^ B := Nat.pow_le_pow_left hk_le B
    _ = 2 ^ (2 * B * Nat.log 2 k) := by rw [← pow_mul]; ring_nf

private theorem log_le_two_mul_log_of_le_pow {E k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ k ^ E) :
    Nat.log 2 n ≤ 2 * E * Nat.log 2 k := by
  have hle : n ≤ 2 ^ (2 * E * Nat.log 2 k) := hn.trans (pow_le_two_pow_two_mul_log E hk)
  exact (Nat.log_mono_right hle).trans_eq (Nat.log_pow Nat.one_lt_two _)

private theorem dist_bool_eq_abs_sub (P₁ P₂ : PMF Bool) :
    dist P₁ P₂ = |(P₁ true).toReal - (P₂ true).toReal| := by
  rw [← coe_nndist, ← Game.advantage_eq_nndist, Game.coe_advantage]
  simp [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]

private theorem dist_bool_le_of_xor_sub_le (P₁ P₂ : PMF Bool) (B : ℝ)
    (h : ∀ pol : Bool,
      ((P₁.map (fun b => b ^^ pol)) true).toReal -
        ((P₂.map (fun b => b ^^ pol)) true).toReal ≤ B) :
    dist P₁ P₂ ≤ B := by
  have hfalse := h false
  have htrue := h true
  have hmap_false (P : PMF Bool) : P.map (fun b => b ^^ false) = P := by
    have hid : (fun b : Bool => b ^^ false) = id := by funext b; simp
    rw [hid, PMF.map_id]
  have hfalse_eq (P : PMF Bool) : (P false).toReal = 1 - (P true).toReal := by
    rw [← PMF.sum_toReal P, Fintype.sum_bool, add_sub_cancel_left]
  have hmap_true (P : PMF Bool) : ((P.map (fun b => b ^^ true)) true).toReal =
      1 - (P true).toReal := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
    simp [hfalse_eq]
  rw [hmap_false, hmap_false] at hfalse
  rw [hmap_true, hmap_true] at htrue
  rw [dist_bool_eq_abs_sub, abs_sub_le_iff]
  exact ⟨hfalse, by linarith⟩

private theorem length_encPair_le_condCoinBudget (c_eval d_eval γ n : ℕ) {w : List Bool}
    (hw : w.length = n + γ * Nat.log 2 n) :
    c_eval * ((encPair encUnary encBits (n, w)).length + 1) ^ d_eval ≤
      condCoinBudget c_eval d_eval γ n := by
  unfold condCoinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, hw]
  omega

/-- Combined conditional PRG distinguishing bound at seed length `n`:
bounds the advantage of `adversary n` between `fullGen` on `condSeedSet` and `uniformList` by the
sum of the LHL core error, the Goldreich–Levin precision error, the prefix fiber hash error, and
the `condInverter` success probability. -/
private theorem dist_condSeedSet_uniform_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ c_eval d_eval deg : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1))
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (adversary : Distinguisher)
    (hlaw : ∀ (a : ℕ × List Bool) length,
      c_eval * ((encPair encUnary encBits a).length + 1) ^ d_eval ≤ length →
      ProbComp.eval (adversary a.1 a.2) = (BitString.uniformList length).map (evaluate a))
    {n : ℕ}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n)
    (hlt_next : n < coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n + 1))
    (hk_2d : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hgap : (r (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)).val +
      d * Nat.log 2 (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hm_le :
      let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
      l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k)
    (hf : ∀ x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n),
      g (List.ofFn x) =
        List.ofFn (ofList (imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
          (g (List.ofFn x))))
    (hS_eq : S (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =
      regularityBucket
        (fun x : BitString (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) =>
          ofList (imgLen (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n))
            (g (List.ofFn x)))
        (r (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)))
    (hdense :
      let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
      2 ^ k ≤ (k + 1) *
        (regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x)))
          (r k)).card) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    let m := mActual d γ k n
    (Game.advantage
      ((((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map
          (fullGen g imgLen d γ_core γ)).bind fun y => ProbComp.eval (adversary n y))
      ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
        fun y => ProbComp.eval (adversary n y)) : ℝ) ≤
      Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) +
      (m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) +
      (m : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) +
      (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
        (Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) := by
  intro k m
  have hfits_k : coreSeedLen imgLen d γ_core k ≤ n := hfits
  have hlt_next_k : n < coreSeedLen imgLen d γ_core (k + 1) := hlt_next
  have hk_2d_k : 2 * (d * Nat.log 2 k) ≤ k := hk_2d
  let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
  let hS_reg : (regularityBucket f (r k)).Nonempty := hS_eq ▸ hS k
  let n_offset := n - coreSeedLen imgLen d γ_core k
  let coinLen := condCoinBudget c_eval d_eval γ n
  have hn_eq : coreSeedLen imgLen d γ_core k + n_offset = n := Nat.add_sub_of_le hfits_k
  have hn_off_le : n_offset ≤ coreSeedLen imgLen d γ_core (k + 1) := by
    dsimp [n_offset]
    omega
  let P₁ : PMF Bool :=
    (((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).bind fun seed =>
        (BitString.uniformList coinLen).map fun coins =>
          evaluate (n, fullGen g imgLen d γ_core γ seed) coins)
  let P₂ : PMF Bool :=
    (BitString.uniformList (n + γ * Nat.log 2 n)).bind fun y =>
      (BitString.uniformList coinLen).map fun coins => evaluate (n, y) coins
  have hreal_eq :
      ((((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map
          (fullGen g imgLen d γ_core γ)).bind fun y => ProbComp.eval (adversary n y)) = P₁ := by
    simp only [P₁, PMF.bind_map, Function.comp_def]
    congr 1; funext x
    have hlen_fg : (fullGen g imgLen d γ_core γ (List.ofFn x)).length = n + γ * Nat.log 2 n := by
      simp [length_fullGen]
    exact hlaw (n, fullGen g imgLen d γ_core γ (List.ofFn x)) coinLen
      (length_encPair_le_condCoinBudget c_eval d_eval γ n hlen_fg)
  have hideal_eq :
      ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
        fun y => ProbComp.eval (adversary n y)) = P₂ := by
    simp only [P₂, BitString.uniformList, PMF.bind_map, Function.comp_def]
    congr 1; funext y
    exact hlaw (n, List.ofFn y) coinLen
      (length_encPair_le_condCoinBudget c_eval d_eval γ n List.length_ofFn)
  rw [hreal_eq, hideal_eq, Game.advantage_eq_nndist, coe_nndist]
  refine dist_bool_le_of_xor_sub_le P₁ P₂ _ fun pol => ?_
  have hP₁_pol :
      P₁.map (fun b => b ^^ pol) =
      (PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
        fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val n_offset m
          coinLen m hm_le := by
    rw [bind_fiberHybridAcceptDist_top_eq g imgLen d γ_core γ S hS r evaluate pol
      hfits hk_2d hf hS_eq hm_le]
    simp [P₁, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hL_split :
      n_offset + k * imgLen k + l1Val d k (r k).val + h2Rows d γ_core k * k +
        l2Val d k (r k).val + m = n + γ * Nat.log 2 n := by
    have h1 : n_offset + k * imgLen k + l1Val d k (r k).val +
        h2Rows d γ_core k * k + l2Val d k (r k).val = lhlPrefixLen d k n :=
      lhlPrefixLen_split imgLen d γ_core (r k).val hfits_k hk_2d_k
    have h2 : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n := by
      have hcs : coreSeedLen imgLen d γ_core k =
          (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
      omega
    have h3 : lhlPrefixLen d k n + m = n + γ * Nat.log 2 n :=
      lhlPrefixLen_add_mActual (γ := γ) h2
    omega
  have hP₂_pol :
      P₂.map (fun b => b ^^ pol) =
      (unifCoreDist k (imgLen k) (l1Val d k (r k).val) (l2Val d k (r k).val)
        (h2Rows d γ_core k)).bind (evalCore evaluate pol n n_offset m coinLen) := by
    rw [unifCoreDist_bind_evalCore_eq _ _ _ _ _ _ _ _ _ _ _ _ hL_split]
    simp [P₂, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hlen0 : l2Val d k (r k).val + 0 ≤ h2Rows d γ_core k := by
    simpa using l2Val_le_h2Rows d γ_core k (r k).val
  let P₀ : PMF Bool :=
    (PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val n_offset m coinLen 0 hlen0
  have hP₀_eq :
      P₀ = (coreLHLDist f (r k) hS_reg (l1Val_le d k (r k).val)
        (l2Val_le_h2Rows d γ_core k (r k).val)).bind
          (evalCore evaluate pol n n_offset m coinLen) :=
    bind_fiberHybridAcceptDist_zero_eq f (r k) hS_reg evaluate pol n d γ_core n_offset m coinLen
      hlen0
  have hdist_core :
      (P₀ true).toReal - ((P₂.map (fun b => b ^^ pol)) true).toReal ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
    have hle_abs :
        (P₀ true).toReal - ((P₂.map (fun b => b ^^ pol)) true).toReal ≤
          dist P₀ (P₂.map (fun b => b ^^ pol)) :=
      (le_abs_self _).trans_eq (dist_bool_eq_abs_sub P₀ (P₂.map (fun b => b ^^ pol))).symm
    refine hle_abs.trans ?_
    rw [hP₀_eq, hP₂_pol]
    refine (PMF.dist_bind_le _ _ _).trans ?_
    exact dist_coreLHLDist_unifCoreDist_le_of_gap f (r k) hS_reg hdense hgap
  have hbucket := bucketHybrid_total_le g imgLen f hf (r k) hS_reg hdense evaluate pol
    d γ_core γ c_eval d_eval deg n_offset n hn_eq hgap hn_off_le hm_le
  rw [hP₁_pol]
  have h1 :
      (((PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
        fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val n_offset m coinLen m
          hm_le) true).toReal - (P₀ true).toReal ≤
      (m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) +
      (m : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) +
      (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
        (Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) := by
    dsimp only [P₀, m, coinLen] at hbucket ⊢
    have hdiv : (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) =
        2 * ((m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) +
          (m : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) := by ring
    linarith
  linarith

/-! ### Theorem 5.5: Existence of a conditional entropy-preserving PRG from any OWF -/

private theorem eventually_coreSeedLen_succ_le_pow {imgLen : ℕ → ℕ} {c_i d_i : ℕ}
    (himg : ∀ k, imgLen k ≤ c_i * (k + 1) ^ d_i) (d γ_core : ℕ) :
    ∀ᶠ k : ℕ in atTop, coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ (d_i + 4) := by
  let M := max 8 (c_i * 2 ^ d_i + 2 * d + γ_core + 4)
  filter_upwards [eventually_ge_atTop M] with k hk
  have hk8 : 8 ≤ k := le_trans (le_max_left _ _) hk
  have hkM : c_i * 2 ^ d_i + 2 * d + γ_core + 4 ≤ k := le_trans (le_max_right _ _) hk
  have hlog : Nat.log 2 (k + 1) ≤ k + 1 := Nat.log_le_self 2 (k + 1)
  have hk2 : k + 2 ≤ 2 * k := by omega
  have hpow2 : (k + 2) ^ d_i ≤ 2 ^ d_i * k ^ d_i := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hk2 d_i
  have himg_k1 : imgLen (k + 1) ≤ k ^ (d_i + 1) := by
    calc
      imgLen (k + 1) ≤ c_i * (k + 2) ^ d_i := himg (k + 1)
      _ ≤ c_i * (2 ^ d_i * k ^ d_i) := Nat.mul_le_mul_left c_i hpow2
      _ = (c_i * 2 ^ d_i) * k ^ d_i := by ring
      _ ≤ k * k ^ d_i := Nat.mul_le_mul_right (k ^ d_i) (by omega)
      _ = k ^ (d_i + 1) := (pow_succ' k d_i).symm
  have hterm_img : (k + 1) * imgLen (k + 1) ≤ 2 * k ^ (d_i + 2) := by
    calc
      (k + 1) * imgLen (k + 1) ≤ (2 * k) * k ^ (d_i + 1) :=
        Nat.mul_le_mul (by omega) himg_k1
      _ = 2 * k ^ (d_i + 2) := by rw [pow_succ' k (d_i + 1)]; ring
  have hh2 : h2Rows d γ_core (k + 1) ≤ 2 * k ^ 2 := by
    have hm : mMax d γ_core (k + 1) ≤ (2 * d + γ_core + 2) * (k + 1) := by
      unfold mMax
      nlinarith
    have hh : h2Rows d γ_core (k + 1) ≤ (2 * d + γ_core + 3) * (k + 1) := by
      unfold h2Rows
      linarith
    calc
      h2Rows d γ_core (k + 1) ≤ (2 * d + γ_core + 3) * (k + 1) := hh
      _ ≤ k * (2 * k) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * k ^ 2 := by ring
  have hterm_h2 : h2Rows d γ_core (k + 1) * (k + 1) ≤ 4 * k ^ 3 := by
    calc
      h2Rows d γ_core (k + 1) * (k + 1) ≤ (2 * k ^ 2) * (2 * k) :=
        Nat.mul_le_mul hh2 (by omega)
      _ = 4 * k ^ 3 := by ring
  have hpow_le2 : k ^ (d_i + 2) ≤ k ^ (d_i + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_le3 : k ^ 3 ≤ k ^ (d_i + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hreg : regWidth (k + 1) + (k + 1) ≤ 2 * k ^ (d_i + 3) := by
    unfold regWidth
    nlinarith
  calc
    coreSeedLen imgLen d γ_core (k + 1)
      = (regWidth (k + 1) + (k + 1)) + (k + 1) * imgLen (k + 1) +
          h2Rows d γ_core (k + 1) * (k + 1) := by
        unfold coreSeedLen; ring
    _ ≤ 2 * k ^ (d_i + 3) + 2 * k ^ (d_i + 3) + 4 * k ^ (d_i + 3) := by linarith
    _ = 8 * k ^ (d_i + 3) := by ring
    _ ≤ k * k ^ (d_i + 3) := Nat.mul_le_mul_right _ hk8
    _ = k ^ (d_i + 4) := (pow_succ' k (d_i + 3)).symm

private theorem sqrt_lhl_err_le {E δ k n : ℕ} (hk : 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E) :
    let d := 2 * (E * (2 * δ + 4) + 4)
    Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
      1 / (4 * (n : ℝ) ^ (δ + 2)) := by
  intro d
  set B := E * (2 * δ + 4) + 4
  have hpow2 : k ^ B ≤ 2 ^ (d * Nat.log 2 k) := by
    simpa [d, mul_assoc] using pow_le_two_pow_two_mul_log B (by omega : 2 ≤ k)
  have hk1 : 2 * (k + 1) ≤ k ^ 2 := by nlinarith
  have hk16 : 16 ≤ k ^ 2 := by nlinarith
  have hn_pow : n ^ (2 * δ + 4) ≤ k ^ (E * (2 * δ + 4)) :=
    (Nat.pow_le_pow_left hn (2 * δ + 4)).trans_eq (pow_mul k E (2 * δ + 4)).symm
  have hnat : 2 * (k + 1) * (16 * n ^ (2 * δ + 4)) ≤ 2 ^ (d * Nat.log 2 k) := by
    calc
      2 * (k + 1) * (16 * n ^ (2 * δ + 4))
        ≤ k ^ 2 * (k ^ 2 * k ^ (E * (2 * δ + 4))) :=
          Nat.mul_le_mul hk1 (Nat.mul_le_mul hk16 hn_pow)
      _ = k ^ B := by
        dsimp [B]
        simp only [pow_add]
        ring
      _ ≤ 2 ^ (d * Nat.log 2 k) := hpow2
  have hreal : (2 * (k + 1 : ℝ)) * (4 * (n : ℝ) ^ (δ + 2)) ^ 2 ≤
      (2 : ℝ) ^ (d * Nat.log 2 k) := by
    have h1 : (2 * (k + 1 : ℝ)) * (16 * (n : ℝ) ^ (2 * δ + 4)) ≤
        (2 : ℝ) ^ (d * Nat.log 2 k) := by exact_mod_cast hnat
    have h2 : (4 * (n : ℝ) ^ (δ + 2)) ^ 2 = 16 * (n : ℝ) ^ (2 * δ + 4) := by ring
    rwa [h2]
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hsq : 2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k) ≤
      (1 / (4 * (n : ℝ) ^ (δ + 2))) ^ 2 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))

private theorem gl_err_le {E δ k n m : ℕ} (hk : 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E)
    (hm : m ≤ n ^ 2) :
    let deg := E * (δ + 2) + 2
    (m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) ≤ 1 / (4 * (n : ℝ) ^ δ) := by
  intro deg
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have h4 : 4 ≤ k ^ 2 := by nlinarith
  have hn_pow : n ^ (δ + 2) ≤ k ^ (E * (δ + 2)) :=
    (Nat.pow_le_pow_left hn (δ + 2)).trans_eq (pow_mul k E (δ + 2)).symm
  have hnat : 4 * n ^ δ * m ≤ 2 * GoldreichLevin.precision deg k := by
    calc
      4 * n ^ δ * m ≤ 4 * n ^ δ * n ^ 2 := Nat.mul_le_mul_left _ hm
      _ = 4 * n ^ (δ + 2) := by rw [pow_add]; ring
      _ ≤ k ^ 2 * k ^ (E * (δ + 2)) := Nat.mul_le_mul h4 hn_pow
      _ = k ^ deg := by dsimp [deg]; rw [pow_add]; ring
      _ ≤ (k + 1) ^ deg := Nat.pow_le_pow_left (by omega) deg
      _ ≤ 2 * (k + 1) ^ deg := by omega
  have hreal : (m : ℝ) * (4 * (n : ℝ) ^ δ) ≤ 2 * (GoldreichLevin.precision deg k : ℝ) := by
    have h1 : (4 * (n : ℝ) ^ δ) * (m : ℝ) ≤ 2 * (GoldreichLevin.precision deg k : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hpos_gl : (0 : ℝ) < 2 * (GoldreichLevin.precision deg k : ℝ) := by
    have := GoldreichLevin.precision_pos deg k
    positivity
  rw [div_le_div_iff₀ hpos_gl (by positivity)]
  linarith

private theorem inv_term_le {E δ d γ_core k n m cs_succ : ℕ} {succProb : ℝ}
    (hk : 2 * d + γ_core + 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E)
    (hcs : cs_succ ≤ k ^ E) (hm : m ≤ mMax d γ_core k) (hsucc_nonneg : 0 ≤ succProb)
    (hsucc : succProb ≤
      1 / ((k + 1 : ℝ) ^ ((2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ))) :
    (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
      (dyadicSize cs_succ : ℝ) * (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) * succProb ≤
      1 / (4 * (n : ℝ) ^ δ) := by
  set D_inv := (2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ
  have hk8 : 8 ≤ k := by omega
  have hlog_k : Nat.log 2 k ≤ k := Nat.log_le_self 2 k
  have hm_ub : m ≤ (2 * d + γ_core + 1) * Nat.log 2 k + 1 := by
    have : mMax d γ_core k = (2 * d + γ_core + 1) * Nat.log 2 k + 1 := by
      unfold mMax; ring
    omega
  have h1 : 2 ^ (m + 1) ≤ k ^ (2 * d + γ_core + 2) := by
    have hm1 : m + 1 ≤ (2 * d + γ_core + 1) * Nat.log 2 k + 2 := by omega
    calc
      2 ^ (m + 1) ≤ 2 ^ ((2 * d + γ_core + 1) * Nat.log 2 k + 2) :=
        Nat.pow_le_pow_right Nat.zero_lt_two hm1
      _ = 4 * 2 ^ ((2 * d + γ_core + 1) * Nat.log 2 k) := by rw [pow_add]; ring
      _ ≤ k * k ^ (2 * d + γ_core + 1) :=
        Nat.mul_le_mul (by omega) (two_pow_mul_log_le_pow (2 * d + γ_core + 1) (by omega))
      _ = k ^ (2 * d + γ_core + 2) := (pow_succ' k (2 * d + γ_core + 1)).symm
  have h2 : dyadicSize m ≤ k ^ 3 := by
    have hm_k2 : m + 1 ≤ 2 * k ^ 2 := by
      have hm_le_k : m + 1 ≤ (2 * d + γ_core + 2) * k := by nlinarith
      calc
        m + 1 ≤ (2 * d + γ_core + 2) * k := hm_le_k
        _ ≤ k * k := Nat.mul_le_mul_right k (by omega)
        _ ≤ 2 * k ^ 2 := by nlinarith
    calc
      dyadicSize m ≤ 2 * (m + 1) := dyadicSize_le m
      _ ≤ 4 * k ^ 2 := by omega
      _ ≤ k * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = k ^ 3 := (pow_succ' k 2).symm
  have h3 : dyadicSize cs_succ ≤ k ^ (E + 1) := by
    have hke_pos : 1 ≤ k ^ E := Nat.one_le_pow E k (by omega)
    calc
      dyadicSize cs_succ ≤ 2 * (cs_succ + 1) := dyadicSize_le cs_succ
      _ ≤ 4 * k ^ E := by omega
      _ ≤ k * k ^ E := Nat.mul_le_mul_right _ (by omega)
      _ = k ^ (E + 1) := (pow_succ' k E).symm
  have h4 : dyadicSize (k + 1) ≤ k ^ 2 := by
    have := dyadicSize_le (k + 1)
    nlinarith
  have h5 : 4 * (k + 1) ≤ k ^ 2 := by nlinarith
  have h6 : n ^ δ ≤ k ^ (E * δ) :=
    (Nat.pow_le_pow_left hn δ).trans_eq (pow_mul k E δ).symm
  have hprod_nat :
      2 ^ (m + 1) * dyadicSize m * dyadicSize cs_succ *
        dyadicSize (k + 1) * (4 * (k + 1)) * n ^ δ ≤ (k + 1) ^ D_inv := by
    calc
      2 ^ (m + 1) * dyadicSize m * dyadicSize cs_succ *
          dyadicSize (k + 1) * (4 * (k + 1)) * n ^ δ
        ≤ k ^ (2 * d + γ_core + 2) * k ^ 3 * k ^ (E + 1) * k ^ 2 * k ^ 2 * k ^ (E * δ) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4) h5) h6
      _ = k ^ D_inv := by
        dsimp [D_inv]
        simp only [pow_add]
      _ ≤ (k + 1) ^ D_inv := Nat.pow_le_pow_left (by omega) D_inv
  let Pref : ℝ := (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
    (dyadicSize cs_succ : ℝ) * (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ)
  have hPref_nonneg : 0 ≤ Pref := by dsimp [Pref]; positivity
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hprod_real : Pref * (4 * (n : ℝ) ^ δ) ≤ (k + 1 : ℝ) ^ D_inv := by
    have hcast : (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) * (dyadicSize cs_succ : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (4 * (k + 1 : ℝ)) * (n : ℝ) ^ δ ≤
        (k + 1 : ℝ) ^ D_inv := by exact_mod_cast hprod_nat
    dsimp [Pref]
    linarith
  have hPref_div : Pref * (1 / (k + 1 : ℝ) ^ D_inv) ≤ 1 / (4 * (n : ℝ) ^ δ) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc
    (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize cs_succ : ℝ) * (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) * succProb
      = (1 / 2) * Pref * succProb := by dsimp [Pref]; ring
    _ ≤ Pref * succProb :=
        mul_le_mul_of_nonneg_right (by linarith) hsucc_nonneg
    _ ≤ Pref * (1 / (k + 1 : ℝ) ^ D_inv) :=
        mul_le_mul_of_nonneg_left hsucc hPref_nonneg
    _ ≤ 1 / (4 * (n : ℝ) ^ δ) := hPref_div

/-- **[Liu and Pass, Theorem 5.5, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]: Every one-way
function yields a conditional entropy-preserving pseudorandom generator.**
For every one-way function $f : \{0, 1\}^* \to \{0, 1\}^*$ and every prescribed polynomial
security exponent $\delta \in \mathbb{N}$ and stretch constant $\gamma \in \mathbb{N}$, there
exist a deterministic polynomial-time generator $G : \{0, 1\}^* \to \{0, 1\}^*$ and an
entropy-loss constant $\alpha \in \mathbb{N}$ such that $G$ is a $(1 / n^\delta, \gamma)$-condEP-PRG
with entropy loss $\alpha$. -/
theorem OneWay.exists_condEPPRG {f : List Bool → List Bool} (hf : OneWay f) (δ γ : ℕ) :
    ∃ (G : List Bool → List Bool) (α : ℕ),
      CondEPPRG G (fun n => 1 / (n : ℝ) ^ δ) γ α := by
  obtain ⟨g, imgLen, hg, himgLen, himgLen_poly⟩ := hf.exists_fixedOutputLength
  obtain ⟨c_i, d_i, himg_raw⟩ := hg.polyTime.polyBounded_length.exists_le
  have himg_le : ∀ k, imgLen k ≤ c_i * (k + 1) ^ d_i := fun k => by
    simpa [himgLen] using himg_raw (List.replicate k false)
  let E := d_i + 4
  let γ_core := γ * (2 * E)
  let d := 2 * (E * (2 * δ + 4) + 4)
  let α := 2 * d + 4
  let deg := E * (δ + 2) + 2
  let f_fin (k : ℕ) (x : BitString k) : BitString (imgLen k) :=
    ofList (imgLen k) (g (List.ofFn x))
  have hbucket (k : ℕ) := exists_regularity_bucket (f_fin k)
  let r (k : ℕ) : Fin (k + 1) := (hbucket k).choose
  let S (k : ℕ) : Finset (BitString k) := regularityBucket (f_fin k) (r k)
  have hS (k : ℕ) : (S k).Nonempty := (hbucket k).choose_spec.1
  have hdense (k : ℕ) : 2 ^ k ≤ (k + 1) * (S k).card := (hbucket k).choose_spec.2.1
  refine ⟨fullGen g imgLen d γ_core γ, α,
    computableInPolyTime_fullGen hg.polyTime.tidy himgLen_poly.tidy d γ_core γ,
    length_fullGen g imgLen d γ_core γ,
    condSeedSet imgLen d γ_core S r, condSeedSet_nonempty imgLen d γ_core S hS r, ?_, ?_⟩
  · intro adversary hadv
    obtain ⟨c_eval, d_eval, evaluate, hevaluate, -, hlaw⟩ := hadv.exists_total_seeded_evaluator
    let D_inv := (2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ
    have hinv_ppt : IsPPT encBits
        (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) :=
      isPPT_condInverter hg.polyTime.tidy himgLen_poly.tidy hevaluate d γ_core γ c_eval d_eval deg
    have hinv_neg :=
      (hg.inversion_negligible _ hinv_ppt).eventually_le_inv_polynomial
        (p := fun k => (k + 1) ^ D_inv) (by fun_prop) (fun k => by positivity)
    have hparam_tendsto := GeneratorReindex.parameter_tendsto (coreSeedLen imgLen d γ_core)
    have hev_k : ∀ᶠ k : ℕ in atTop,
        (2 * d + γ_core + γ + 8 ≤ k) ∧
        (0 + 2 * d * Nat.log 2 k ≤ k) ∧
        ((r k).val + d * Nat.log 2 k ≤ k) ∧
        (coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E) ∧
        ((Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) ≤
          1 / ((k + 1 : ℝ) ^ D_inv)) := by
      filter_upwards [eventually_ge_atTop (2 * d + γ_core + γ + 8),
        Nat.eventually_add_mul_log_le 0 (2 * d) Nat.one_lt_two,
        eventually_regularity_gap hg himgLen r hdense d,
        eventually_coreSeedLen_succ_le_pow himg_le d γ_core,
        hinv_neg] with k hk1 hk2 hk3 hk4 hk5
      refine ⟨hk1, hk2, hk3, hk4, ?_⟩
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hk5
    filter_upwards [eventually_ge_atTop (coreSeedLen imgLen d γ_core 0),
      hparam_tendsto.eventually hev_k] with n hn0 ⟨hk_min, hk_2d', hgap, hcs_pow, hinv_le⟩
    set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    have hfits : coreSeedLen imgLen d γ_core k ≤ n := GeneratorReindex.parameter_fits hn0
    have hlt_next : n < coreSeedLen imgLen d γ_core (k + 1) :=
      GeneratorReindex.lt_length_succ_parameter (coreSeedLen_ge_succ imgLen d γ_core) n
    have hk_2d : 2 * (d * Nat.log 2 k) ≤ k := by linarith [hk_2d']
    have hn_le_pow : n ≤ k ^ E := hlt_next.le.trans hcs_pow
    have hk_lt_n : k < n :=
      lt_of_lt_of_le (Nat.lt_succ_self k) ((coreSeedLen_ge_succ imgLen d γ_core k).trans hfits)
    have hn_pos : 1 ≤ n := by omega
    have hlog_le : Nat.log 2 n ≤ 2 * E * Nat.log 2 k :=
      log_le_two_mul_log_of_le_pow (by omega : 2 ≤ k) hn_le_pow
    have hm_le_mMax : mActual d γ k n ≤ mMax d γ_core k := by
      apply mActual_le_mMax
      dsimp [γ_core]
      nlinarith
    have hm_le : l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k := by
      have := l2Val_le d k (r k).val
      unfold h2Rows
      omega
    have hm_le_n2 : mActual d γ k n ≤ n ^ 2 := by
      have hcs : coreSeedLen imgLen d γ_core k =
          (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
      have h1 : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n := by omega
      have h2 : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
      have h3 : mActual d γ k n ≤ (γ + 1) * n := by
        unfold mActual
        nlinarith
      have h4 : (γ + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
      calc
        mActual d γ k n ≤ (γ + 1) * n := h3
        _ ≤ n * n := h4
        _ = n ^ 2 := (sq n).symm
    have hf_k (x : BitString k) : g (List.ofFn x) = List.ofFn (f_fin k x) := by
      refine (ofFn_ofList ?_).symm
      simp [himgLen]
    have hdist := dist_condSeedSet_uniform_le g imgLen d γ_core γ c_eval d_eval deg
      S hS r evaluate adversary hlaw hfits hlt_next hk_2d hgap hm_le hf_k rfl (hdense k)
    dsimp only at hdist
    have hlhl_err := sqrt_lhl_err_le (δ := δ) (by omega : 8 ≤ k) hn_pos hn_le_pow
    have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hn_pow_le : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (δ + 2) := by
      exact_mod_cast Nat.pow_le_pow_right hn_pos (by omega : δ ≤ δ + 2)
    have hterm1 : Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
        1 / (4 * (n : ℝ) ^ δ) := by
      refine hlhl_err.trans (one_div_le_one_div_of_le (by positivity) ?_)
      linarith
    have hterm2 : (mActual d γ k n : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) ≤
        1 / (4 * (n : ℝ) ^ δ) :=
      gl_err_le (by omega) hn_pos hn_le_pow hm_le_n2
    have hterm3 : (mActual d γ k n : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
        1 / (4 * (n : ℝ) ^ δ) := by
      have hsqrt_le : Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
          1 / (4 * (n : ℝ) ^ (δ + 2)) := by
        refine (Real.sqrt_le_sqrt ?_).trans hlhl_err
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hm_r : (mActual d γ k n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hm_le_n2
      calc
        (mActual d γ k n : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))
          ≤ (n : ℝ) ^ 2 * (1 / (4 * (n : ℝ) ^ (δ + 2))) :=
            mul_le_mul hm_r hsqrt_le (by positivity) (by positivity)
        _ = 1 / (4 * (n : ℝ) ^ δ) := by
            rw [pow_add (n : ℝ) δ 2]
            field_simp
    have hterm4 :
        (1 / 2) * (2 : ℝ) ^ (mActual d γ k n + 1) * (dyadicSize (mActual d γ k n) : ℝ) *
          (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
          (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
          (Game.succProbability (ProbComp.eval
            (inversionGame g
              (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) ≤
        1 / (4 * (n : ℝ) ^ δ) :=
      inv_term_le (by omega) hn_pos hn_le_pow hcs_pow hm_le_mMax
        (by positivity) hinv_le
    have hsum4 : 4 * (1 / (4 * (n : ℝ) ^ δ)) = 1 / (n : ℝ) ^ δ := by ring
    dsimp only [k] at hterm1 hterm2 hterm3 hterm4
    linarith
  · have hparam_tendsto := GeneratorReindex.parameter_tendsto (coreSeedLen imgLen d γ_core)
    have hev_k : ∀ᶠ k : ℕ in atTop,
        (8 ≤ k) ∧
        (0 + 2 * d * Nat.log 2 k ≤ k) ∧
        ((r k).val + d * Nat.log 2 k ≤ k) ∧
        (coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E) := by
      filter_upwards [eventually_ge_atTop 8,
        Nat.eventually_add_mul_log_le 0 (2 * d) Nat.one_lt_two,
        eventually_regularity_gap hg himgLen r hdense d,
        eventually_coreSeedLen_succ_le_pow himg_le d γ_core] with k hk1 hk2 hk3 hk4
      exact ⟨hk1, hk2, hk3, hk4⟩
    filter_upwards [eventually_ge_atTop (coreSeedLen imgLen d γ_core 0),
      Nat.eventually_le_log 1 Nat.one_lt_two,
      hparam_tendsto.eventually hev_k] with n hn0 hlog_n1 ⟨hk8, hk_2d', hgap, hcs_pow⟩
    set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    have hfits : coreSeedLen imgLen d γ_core k ≤ n := GeneratorReindex.parameter_fits hn0
    have hlt_next : n < coreSeedLen imgLen d γ_core (k + 1) :=
      GeneratorReindex.lt_length_succ_parameter (coreSeedLen_ge_succ imgLen d γ_core) n
    have hk_2d : 2 * (d * Nat.log 2 k) ≤ k := by linarith [hk_2d']
    have hn_le_pow : n ≤ k ^ E := hlt_next.le.trans hcs_pow
    have hk_lt_n : k < n :=
      lt_of_lt_of_le (Nat.lt_succ_self k) ((coreSeedLen_ge_succ imgLen d γ_core k).trans hfits)
    have hn_pos : 1 ≤ n := by omega
    have hcs_def : coreSeedLen imgLen d γ_core k =
        (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
    have hh2_pos : 1 ≤ h2Rows d γ_core k * k := by unfold h2Rows; nlinarith
    have hlhl_pos : 1 ≤ lhlPrefixLen d k n := by
      unfold lhlPrefixLen
      omega
    have hlhl_le_n : lhlPrefixLen d k n ≤ n := by
      unfold lhlPrefixLen
      omega
    have hdist_core :
        dist (coreLHLDist (f_fin k) (r k) (hS k) (l1Val_le d k (r k).val)
            (l2Val_le_h2Rows d γ_core k (r k).val))
          (unifCoreDist k (imgLen k) (l1Val d k (r k).val) (l2Val d k (r k).val)
            (h2Rows d γ_core k)) ≤ 1 / (lhlPrefixLen d k n : ℝ) ^ 2 := by
      refine (dist_coreLHLDist_unifCoreDist_le_of_gap
        (f_fin k) (r k) (hS k) (hdense k) hgap).trans ?_
      refine (sqrt_lhl_err_le (δ := δ) hk8 hn_pos hn_le_pow).trans ?_
      have hlhl_rpos : (0 : ℝ) < (lhlPrefixLen d k n : ℝ) ^ 2 := by positivity
      refine one_div_le_one_div_of_le hlhl_rpos ?_
      have h1 : (lhlPrefixLen d k n) ^ 2 ≤ 4 * n ^ (δ + 2) := by
        calc
          (lhlPrefixLen d k n) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hlhl_le_n 2
          _ ≤ n ^ (δ + 2) := Nat.pow_le_pow_right hn_pos (by omega)
          _ ≤ 4 * n ^ (δ + 2) := by omega
      exact_mod_cast h1
    have hg_len_k (x : BitString k) : (g (List.ofFn x)).length = imgLen k := by
      simp [himgLen]
    have hent := entropy_fullGen_condSeedSet_ge g imgLen d γ_core γ S hS r hfits hk_2d
      hg_len_k rfl hdist_core
    dsimp only at hent
    have hlog_kn : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hk_lt_n.le
    have hsub_le : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n := by omega
    have hlhl_cast : (lhlPrefixLen d k n : ℝ) =
        (n : ℝ) - (2 * (d : ℝ) * (Nat.log 2 k : ℝ) + (Nat.log 2 k : ℝ) + 1) := by
      unfold lhlPrefixLen
      rw [Nat.cast_sub hsub_le]
      push_cast
      ring
    have hloss_le : (n : ℝ) - (α : ℝ) * (Nat.log 2 n : ℝ) ≤ (lhlPrefixLen d k n : ℝ) - 2 := by
      rw [hlhl_cast]
      have hlog_kn_r : (Nat.log 2 k : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlog_kn
      have hlog_n1_r : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlog_n1
      have hα_def : (α : ℝ) = 2 * (d : ℝ) + 4 := by dsimp [α]; push_cast; ring
      rw [hα_def]
      nlinarith
    exact hloss_le.trans hent

end Cslib.Crypto
