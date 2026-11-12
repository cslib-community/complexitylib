/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Negligible
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.Entropy
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogTwoPow
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Uniform

/-!
# Real sample entropy and accessible average max-entropy

For a deterministic function $F : \alpha \to \beta$ on a finite uniform domain
$X \leftarrow \alpha$, the **real sample entropy** of $x \in \alpha$ (`realSampleEntropy F x`) is
$\log_2 |F^{-1}(F(x))|$ (`[HHRVW2020]`, Definition 3.1, p. 11); its expectation over uniform
$X \leftarrow \alpha$ equals the conditional Shannon entropy $H(X \mid F(X))$
(`expected_realSampleEntropy_eq_conditionalEntropy`).

An **$F$-collision-finder** (`IsCollisionFinder F A`) is a randomized mapping supported on the
preimage fiber $F^{-1}(F(x))$ (`[HHRVW2020]`, Definition 3.3, p. 12); any randomized mapping is
canonically sanitized to an $F$-collision-finder by falling back to $x$ on non-colliding outputs
(`sanitizeCollisionFinder`, `[HHRVW2020]`, Definition 3.3 and fallback discussion, p. 12).

A single family of subsets $L(x) \subseteq F^{-1}(F(x))$ with $x \in L(x)$ witnesses **accessible
average max-entropy** at most $\mathbb{E}_{X}[\log_2 |L(X)|]$ (`accessibleSetExpectation L`; cf.
`[HHRVW2020]`, Definition 3.9, p. 15, which allows $L$ to depend on the collision-finder, whereas
`InaccessibleEntropyFamily` fixes one family `accSet n` against all uniform strict-PPT adversaries
in `accessibleEscapeGame`). The elementary inequality $-\log_2(1 - \alpha) \ge \alpha$ for
$\alpha \in [0, 1)$ lower-bounds the entropy gap $H(X \mid F(X)) - \mathbb{E}[\log_2 |L(X)|]$ by the
expected fraction of fiber elements outside $L(X)$
(`conditionalEntropy_sub_accessibleSetExpectation_ge`, `[HHRVW2020]`, Section 4.2, p. 24).

## Main definitions

* `Cslib.Crypto.fiberSet`: preimage fiber $F^{-1}(y)$ as a `Finset`.
* `Cslib.Crypto.realSampleEntropy`: $\log_2 |F^{-1}(F(x))|$.
* `Cslib.Crypto.IsCollisionFinder`, `Cslib.Crypto.sanitizeCollisionFinder`: collision-finding
  randomized mappings and canonical fallback sanitization.
* `Cslib.Crypto.accessibleSetExpectation`: $\mathbb{E}_{X \leftarrow \alpha}[\log_2 |L(X)|]$.
* `Cslib.Crypto.accessibleEscapeGame`: security experiment testing whether an adversary outputs a
  fixed-width colliding preimage outside `accSet`.
* `Cslib.Crypto.InaccessibleEntropyFamily`: uniform polynomial-time function family with a
  $1 / \mathrm{denom}(n)$ gap between real Shannon entropy and accessible average max-entropy.

## Main results

* `Cslib.Crypto.expected_realSampleEntropy_eq_conditionalEntropy`: expected real sample entropy over
  a uniform input equals `PMF.conditionalEntropy`.
* `Cslib.Crypto.isCollisionFinder_sanitizeCollisionFinder`: `sanitizeCollisionFinder` always outputs
  a preimage in $F^{-1}(F(x))$.
* `Cslib.Crypto.conditionalEntropy_sub_accessibleSetExpectation_ge`: lower bound on
  $H(X \mid F(X)) - \mathbb{E}[\log_2 |L(X)|]$ from the average fiber-escape density.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 3 (Definitions 3.1, 3.3, 3.9, pp. 11–15)
  and Section 4.2 (Theorem 4.5, p. 21)][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset
open scoped ENNReal

/-! ### Preimage fibers and real sample entropy -/

/-- Preimage fiber $F^{-1}(y) = \{x \in \alpha \mid F(x) = y\}$ of a finite-domain map. -/
@[expose] def fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (y : β) :
    Finset α :=
  univ.filter fun x => F x = y

@[simp] theorem mem_fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (y : β)
    (x : α) : x ∈ fiberSet F y ↔ F x = y := by
  simp [fiberSet]

theorem self_mem_fiberSet {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (x : α) :
    x ∈ fiberSet F (F x) := by
  simp [fiberSet]

theorem card_fiberSet_pos {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β) (x : α) :
    0 < #(fiberSet F (F x)) :=
  card_pos.mpr ⟨x, self_mem_fiberSet F x⟩

theorem card_fiberSet_eq_fintypeCard {α β : Type*} [Fintype α] [DecidableEq β] (F : α → β)
    (y : β) : #(fiberSet F y) = Fintype.card {x : α // F x = y} :=
  (Fintype.card_of_subtype (fiberSet F y) fun _ => mem_fiberSet F y _).symm

/-- **Real sample entropy** $\log_2 |F^{-1}(F(x))|$ of an input $x$ under uniform sampling on
$\alpha$ (`[HHRVW2020]`, Section 3.1, Definition 3.1, p. 11). -/
@[expose] noncomputable def realSampleEntropy {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : ℝ :=
  Real.logb 2 #(fiberSet F (F x))

theorem realSampleEntropy_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : 0 ≤ realSampleEntropy F x :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast card_fiberSet_pos F x)

theorem realSampleEntropy_le_log_card {α β : Type*} [Fintype α] [DecidableEq β]
    (F : α → β) (x : α) : realSampleEntropy F x ≤ Real.logb 2 (Fintype.card α) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast card_fiberSet_pos F x)
  exact_mod_cast card_le_univ (fiberSet F (F x))

/-- Averaging `realSampleEntropy F` over a uniform input recovers the Shannon conditional entropy
$H(X \mid F(X))$ (`[HHRVW2020]`, Section 3.1, p. 11). -/
theorem expected_realSampleEntropy_eq_conditionalEntropy {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (F : α → β) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy F x) =
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) := by
  classical
  let := Fintype.ofFinite β
  rw [PMF.conditionalEntropy_eq_sum_surprisal,
    PMF.sum_map_mul (PMF.uniformOfFintype α) (fun x => (F x, x))
      (fun pair => PMF.surprisal
        (PMF.conditionalSnd ((PMF.uniformOfFintype α).map fun a => (F a, a)) pair.1) pair.2)]
  refine sum_congr rfl fun x _ => congrArg (((PMF.uniformOfFintype α) x).toReal * ·) ?_
  dsimp only
  have : Nonempty {a : α // F a = F x} := ⟨⟨x, rfl⟩⟩
  have hcond := congrArg (fun p : PMF α => PMF.surprisal p x)
    (PMF.conditionalSnd_uniform_map F (F x))
  rw [hcond]
  let clsFin : Fintype {a : α // F a = F x} :=
    @Subtype.fintype α (fun a => F a = F x) (Classical.decPred _) ‹_›
  have hmap : ((@PMF.uniformOfFintype {a : α // F a = F x} clsFin _).map Subtype.val) x =
      (@PMF.uniformOfFintype {a : α // F a = F x} clsFin _) ⟨x, rfl⟩ := by
    rw [PMF.map_apply, tsum_eq_single ⟨x, rfl⟩]
    · simp
    · intro b hb
      have hval : x ≠ b.1 := fun h => hb (Subtype.ext h.symm)
      simp [hval]
  rw [realSampleEntropy, PMF.surprisal]
  change Real.logb 2 #(fiberSet F (F x)) =
    -Real.logb 2 (((@PMF.uniformOfFintype {a : α // F a = F x} clsFin _).map Subtype.val) x).toReal
  rw [hmap, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Real.logb_inv, neg_neg]
  congr 2
  rw [card_fiberSet_eq_fintypeCard, Subsingleton.elim (Subtype.fintype fun a => F a = F x) clsFin]

/-! ### Collision-finding adversaries and canonical sanitization -/

/-- An **$F$-collision-finder** is a randomized mapping that always outputs a preimage in the fiber
$F^{-1}(F(x))$ (`[HHRVW2020]`, Section 3.1, Definition 3.3, p. 12). -/
@[expose] def IsCollisionFinder {α β : Type*} (F : α → β) (A : α → PMF α) : Prop :=
  ∀ x x', x' ∈ (A x).support → F x' = F x

/-- Canonical fallback sanitization replacing any non-colliding output of `A x` by `x` itself
(`[HHRVW2020]`, Section 3.1, Definition 3.3 and fallback discussion, p. 12). -/
@[expose] noncomputable def sanitizeCollisionFinder {α β : Type*} [DecidableEq β]
    (F : α → β) (A : α → PMF α) (x : α) : PMF α :=
  (A x).map fun x' => if F x' = F x then x' else x

theorem isCollisionFinder_sanitizeCollisionFinder {α β : Type*} [DecidableEq β]
    (F : α → β) (A : α → PMF α) : IsCollisionFinder F (sanitizeCollisionFinder F A) := by
  intro x y hy
  obtain ⟨x', _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  split_ifs with h
  · exact h
  · rfl

/-! ### Accessible set expectation and the fiber-escape entropy gap -/

/-- Expected base-$2$ log-cardinality $\mathbb{E}_{X \leftarrow \alpha}[\log_2 |L(X)|]$ of a family
of accessible preimage sets (`[HHRVW2020]`, Section 3.2, Definition 3.9, p. 15). -/
@[expose] noncomputable def accessibleSetExpectation {α : Type*} [Fintype α] [Nonempty α]
    (L : α → Finset α) : ℝ :=
  ∑ x : α, ((PMF.uniformOfFintype α) x).toReal * Real.logb 2 #(L x)

theorem accessibleSetExpectation_nonneg {α : Type*} [Fintype α] [Nonempty α]
    (L : α → Finset α) : 0 ≤ accessibleSetExpectation L :=
  sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
    (div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg one_le_two))

private theorem sub_div_le_logb_sub {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.logb 2 b - Real.logb 2 a := by
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one (ha.trans hab)
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let α := (b - a) / b
  have hα_nonneg : 0 ≤ α := div_nonneg (sub_nonneg.mpr hab) hb_pos.le
  have h1_sub : 1 - α = a / b := by
    dsimp only [α]
    field_simp [hb_pos.ne']
    ring
  have h1_pos : 0 < 1 - α := by
    rw [h1_sub]
    exact div_pos ha_pos hb_pos
  have hexp : 1 - α ≤ Real.exp (-α) := by
    linarith [Real.add_one_le_exp (-α)]
  have hlog : Real.log (1 - α) ≤ -α := by
    simpa only [Real.log_exp] using Real.log_le_log h1_pos hexp
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_one : Real.log 2 ≤ 1 := Real.log_two_lt_one.le
  have hdiv : α ≤ -Real.log (1 - α) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    nlinarith
  have hlogb : -Real.log (1 - α) / Real.log 2 = Real.logb 2 b - Real.logb 2 a := by
    rw [h1_sub, Real.log_div ha_pos.ne' hb_pos.ne', Real.logb, Real.logb]
    ring
  exact hlogb ▸ hdiv

/-- Pointwise bound behind `[HHRVW2020]`, Claim 4.7 (p. 24): when
$x \in L(x) \subseteq F^{-1}(F(x))$, the gap $\log_2 |F^{-1}(F(x))| - \log_2 |L(x)|$ is at least
$|F^{-1}(F(x)) \setminus L(x)| / |F^{-1}(F(x))|$. -/
theorem expected_realSampleEntropy_sub_accessibleSetExpectation_ge {α β : Type*}
    [Fintype α] [Nonempty α] [DecidableEq α] [DecidableEq β]
    (F : α → β) (L : α → Finset α)
    (hself : ∀ x, x ∈ L x) (hsub : ∀ x, L x ⊆ fiberSet F (F x)) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal *
        ((#(fiberSet F (F x) \ L x) : ℝ) / #(fiberSet F (F x)))) ≤
      (∑ x : α, ((PMF.uniformOfFintype α) x).toReal * realSampleEntropy F x) -
        accessibleSetExpectation L := by
  rw [accessibleSetExpectation, ← sum_sub_distrib]
  refine sum_le_sum fun x _ => ?_
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have ha : (1 : ℝ) ≤ #(L x) := by exact_mod_cast card_pos.mpr ⟨x, hself x⟩
  have hab : (#(L x) : ℝ) ≤ #(fiberSet F (F x)) := by
    exact_mod_cast card_le_card (hsub x)
  have hsdiff : (#(fiberSet F (F x) \ L x) : ℝ) = #(fiberSet F (F x)) - #(L x) := by
    rw [card_sdiff_of_subset (hsub x), Nat.cast_sub (card_le_card (hsub x))]
  rw [hsdiff, realSampleEntropy]
  exact sub_div_le_logb_sub ha hab

/-- Conditional-entropy form of `expected_realSampleEntropy_sub_accessibleSetExpectation_ge`
(`[HHRVW2020]`, Section 4.2, p. 24). -/
theorem conditionalEntropy_sub_accessibleSetExpectation_ge {α β : Type*}
    [Fintype α] [Nonempty α] [DecidableEq α] [Finite β] [DecidableEq β]
    (F : α → β) (L : α → Finset α)
    (hself : ∀ x, x ∈ L x) (hsub : ∀ x, L x ⊆ fiberSet F (F x)) :
    (∑ x : α, ((PMF.uniformOfFintype α) x).toReal *
        ((#(fiberSet F (F x) \ L x) : ℝ) / #(fiberSet F (F x)))) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) -
        accessibleSetExpectation L := by
  rw [← expected_realSampleEntropy_eq_conditionalEntropy F]
  exact expected_realSampleEntropy_sub_accessibleSetExpectation_ge F L hself hsub

/-! ### Computational accessible-escape game and family interface -/

/-- Fixed-width `BitString` view of a word function on `inLen`-bit inputs, truncated or zero-padded
to `outLen` output bits. -/
@[expose] def wordToFinMap (inLen outLen : ℕ) (f : List Bool → List Bool)
    (z : BitString inLen) : BitString outLen :=
  BitString.ofList outLen (f (List.ofFn z))

/-- Security experiment testing whether an adversary `A` outputs an `(inLen n)`-bit colliding
preimage of `evalWord n` outside the accessible set `accSet n`. -/
@[expose] noncomputable def accessibleEscapeGame (evalWord : ℕ → List Bool → List Bool)
    (inLen : ℕ → ℕ)
    (accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : ProbComp Bool := do
  let zWord ← BitString.sampleList (inLen n)
  let raw ← A n zWord
  let z := BitString.ofList (inLen n) zWord
  let z' := BitString.ofList (inLen n) raw
  return decide (raw.length = inLen n ∧ evalWord n raw = evalWord n zWord ∧ z' ∉ accSet n z)

/-- A uniform polynomial-time fixed-width function family with one adversary-independent
accessible-set family `accSet n` exhibiting an eventual `1 / denom n` gap between real conditional
Shannon entropy $H(Z \mid F(Z))$ and $\mathbb{E}[\log_2 |L(Z)|]$ against all uniform strict-PPT
adversaries (cf. `[HHRVW2020]`, Section 3.2, Definition 3.9, p. 15). -/
structure InaccessibleEntropyFamily where
  /-- Input bit width $n_0(n)$ at security parameter $n$. -/
  inLen : ℕ → ℕ
  /-- Output bit width $m_0(n)$ at security parameter $n$. -/
  outLen : ℕ → ℕ
  /-- Inverse entropy-gap denominator $D(n) \ge 1$. -/
  denom : ℕ → ℕ
  /-- Word-level evaluator $(n, z) \mapsto F_0(n, z)$. -/
  evalWord : ℕ → List Bool → List Bool
  /-- Accessible preimage subset $L_0(n, z) \subseteq F_0(n)^{-1}(F_0(n, z))$ for each input $z$. -/
  accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n))
  /-- Plain polynomial-time unary input-length certificate. -/
  polyTime_inLen : Turing.MultiTapeTM.ComputableInPolyTime inLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary output-length certificate. -/
  polyTime_outLen : Turing.MultiTapeTM.ComputableInPolyTime outLen
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Plain polynomial-time unary gap-denominator certificate. -/
  polyTime_denom : Turing.MultiTapeTM.ComputableInPolyTime denom
    Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary
  /-- Positive gap denominator at every security parameter. -/
  denom_pos : ∀ n, 1 ≤ denom n
  /-- Plain polynomial-time word-evaluation certificate. -/
  polyTime_evalWord : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : ℕ × List Bool => evalWord p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)
    Turing.MultiTapeTM.encBits
  /-- Fixed output width `outLen n` on `(inLen n)`-bit inputs. -/
  length_evalWord : ∀ n z, z.length = inLen n → (evalWord n z).length = outLen n
  /-- Reflexivity $z \in L_0(n, z)$ at every input. -/
  self_mem_accSet : ∀ n z, z ∈ accSet n z
  /-- Inclusion $L_0(n, z) \subseteq F_0(n)^{-1}(F_0(n, z))$ at every input. -/
  accSet_subset_fiber : ∀ n z,
    accSet n z ⊆ fiberSet (wordToFinMap (inLen n) (outLen n) (evalWord n))
      (wordToFinMap (inLen n) (outLen n) (evalWord n) z)
  /-- Eventual $1 / \mathrm{denom}(n)$ gap between real Shannon entropy and accessible average
  max-entropy. -/
  eventually_entropy_gap : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
    accessibleSetExpectation (accSet n) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
          (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
        1 / (denom n : ℝ)
  /-- Every uniform strict-PPT adversary has negligible probability of outputting an `(inLen n)`-bit
  colliding preimage outside `accSet n`. -/
  escape_negligible : ∀ A : ℕ → List Bool → ProbComp (List Bool),
    Probability.IsPPT Turing.MultiTapeTM.encBits A →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord inLen accSet A n)))

end Cslib.Crypto
