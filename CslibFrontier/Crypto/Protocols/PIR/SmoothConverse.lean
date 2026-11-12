/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.OneQuery
public import CslibFrontier.Crypto.Protocols.PIR.Basic
public import CslibFrontier.Languages.Probabilistic.Rational
public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smooth codes from private information retrieval schemes

In the converse direction to `PIR.SmoothCode` ([Yekhanin, Lemma 6.2][Yekhanin2012]),
[Goldreich, Karloff, Schulman and Trevisan, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]
(after [Katz and Trevisan][KatzTrevisan2000], restated for perfectly private two-server schemes as
[Kerenidis and de Wolf, Appendix B, Lemma 3][KerenidisDeWolf2004]) converts any one-round PIR
scheme into a smooth code by tabulating all server answers and duplicating heavily queried entries.

Given a one-round scheme `P : PIR.Scheme ι S R Q A` over finite server and query alphabets `S`, `Q`
(`l = |S| · |Q|`) and a reference index `i₀ : ι`:

* **Replicated answer code (`PIR.smoothCode P i₀`).** Each server-query pair `(s, q) : S × Q` has
  rational query probability `p₀(s, q) = ProbComp.evalRat (P.serverQuery s i₀) q` under `i₀` and is
  replicated `smoothCopies P i₀ (s, q) = max 1 ⌈p₀(s, q) · l⌉₊` times in `SmoothPos P i₀`, with
  every copy storing `P.answer s x q`. Because `max 1 ⌈r⌉₊ ≤ 1 + r` for all `r ≥ 0` and
  `∑_{(s, q)} p₀(s, q) = |S|`, the codeword length satisfies
  `|SmoothPos P i₀| ≤ (|S| + 1) · |S| · |Q|` (`card_smoothPos_le`), recovering `m ≤ 6 · |Q|` when
  `|S| = 2` (`card_smoothPos_le_six_mul`).
* **Non-adaptive smooth decoder with statistical-privacy rejection (`PIR.smoothDecoder P i₀`).**
  To decode `x i`, the decoder draws `(r, q) ← P.query i` and a fallback coin `guess` upfront; for
  each server `s`, if `pᵢ(s, q s) ≤ p₀(s, q s)` it picks a uniform copy of `(s, q s)`, whereas if
  `p₀(s, q s) < pᵢ(s, q s)` it keeps `(s, q s)` with exact rational probability `p₀ / pᵢ` via
  `ProbComp.bernoulliRat` and otherwise rejects the slot. If every server slot survives, the
  decoder reads all `|S|` selected positions non-adaptively via `Code.readAll` and runs
  `P.reconstruct i r`; if any slot was rejected, it enters failure mode without querying the
  codeword and outputs `guess`. Thus:
  - each execution makes at most `|S|` non-adaptive queries with oblivious expected reads
    (`isQueryBounded_smoothDecoder`, `hasObliviousReads_smoothDecoder`);
  - each codeword position is read at most `min(p₀, pᵢ) / smoothCopies ≤ 1 / l ≤ (|S| + 1) / m`
    times in expectation (`expectedReads_smoothDecoder_le`);
  - when each server's query distributions are pairwise `δ`-close in total variation (`CloseTo`),
    failure mode occurs with probability at most `|S| · δ` and still guesses `x i` with probability
    `1 / 2`, so `smoothDecoder P i₀` is a `(|S|, |S| + 1, ε - |S| · δ / 2)`-smooth decoder
    (`isSmoothDecoder_smoothDecoder`), specializing at `|S| = 2` to `(2, 3, ε - δ)`
    (`isSmoothDecoder_smoothDecoder_two`, GKST Lemma 7.1) and under perfect privacy (`δ = 0`) to
    `(|S|, |S| + 1, ε)` (`isSmoothDecoder_smoothDecoder_of_isPrivate`) with exact output-law
    preservation (`decodeLaw_smoothDecoder_of_isPrivate`).
* **Structural clauses of GKST Lemma 7.1:**
  - *Item 1 (Linearity):* when server answers are additive in `x`, `smoothCode P i₀` is an
    `AddMonoidHom` (`smoothCode_zero`, `smoothCode_add`, `smoothCodeAddHom`).
  - *Item 2 (Predetermined answer coordinates):* `smoothCoins P i₀ i` exposes the sampled private
    state `st.state : R` alongside the selected positions `st.slots`; when `P.reconstruct i r`
    depends on each `a s : κ → γ` only on a predetermined subset `sel i r s : Finset κ`, masking
    retrieved codeword entries outside `sel i st.state s` leaves `smoothDecoder P i₀ i` unchanged
    (`smoothDecoder_eq_of_predetermined`).
* **Single-server noisy / statistically-private answer bound:** combining
  `isSmoothDecoder_smoothDecoder` at `[Unique S]` (`q = 1, c = 2`) with
  `Code.IsSmoothDecoder.four_mul_card_mul_sq_le` (`OneQuery.lean`) yields
  `|ι| · (ε - δ / 2)² ≤ |A| - 1` (`card_mul_sq_le_card_answer_sub_one_of_statPrivate`, and
  `|ι| · ε² ≤ |A| - 1` under `P.IsPrivate`), complementing `PIR.SingleServer`'s
  perfect-correctness bound `2 ^ |ι| ≤ |A|`.

## Model boundaries

In GKST Definition 2.1, smoothness bounds the probability of querying each position `j` by `c / m`
for a non-adaptive decoder. Here `smoothDecoder P i₀` draws all query positions before making any
oracle call, makes zero queries in failure mode, and otherwise queries one position per distinct
server `s : S`, so no execution queries the same position `j` twice; expected reads and query
probability therefore coincide, and bounding `Code.expectedReads` establishes
`Code.IsSmoothDecoder`. Neither machine running time nor fair-coin simulation of rational `unifFin`
draws is certified here.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.smoothCopies`, `Cslib.Crypto.Protocols.PIR.SmoothPos`,
  `Cslib.Crypto.Protocols.PIR.smoothCode`: replicated PIR answer table and smooth code.
* `Cslib.Crypto.Protocols.PIR.SmoothCoins`, `Cslib.Crypto.Protocols.PIR.smoothKeepRatio`,
  `Cslib.Crypto.Protocols.PIR.smoothCoins`, `Cslib.Crypto.Protocols.PIR.smoothDecoder`:
  GKST non-adaptive smooth decoder and upfront coin draw with statistical-privacy failure mode.
* `Cslib.Crypto.Protocols.PIR.smoothCodeAddHom`: linearity refinement (GKST Lemma 7.1, item 1).

## Main results

* `Cslib.Crypto.Protocols.PIR.card_smoothPos_le`,
  `Cslib.Crypto.Protocols.PIR.card_smoothPos_le_six_mul`: codeword length `≤ (|S| + 1) |S| |Q|`
  (`≤ 6 |Q|` for two servers).
* `Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder`,
  `Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_two`,
  `Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_of_isPrivate`: GKST Lemma 7.1 and
  Kerenidis–de Wolf Appendix B Lemma 3.
* `Cslib.Crypto.Protocols.PIR.decodeLaw_smoothDecoder_of_isPrivate`: exact output law preservation
  under perfect privacy.
* `Cslib.Crypto.Protocols.PIR.smoothCodeAddHom`,
  `Cslib.Crypto.Protocols.PIR.smoothDecoder_eq_of_predetermined`: GKST Lemma 7.1 items 1–2.
* `Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_statPrivate`,
  `Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_isPrivate`: noisy /
  statistically-private single-server answer-alphabet lower bounds.

## References

* [O. Goldreich, H. Karloff, L. J. Schulman, L. Trevisan, *Lower bounds for linear locally
  decodable codes and private information retrieval*][GoldreichKarloffSchulmanTrevisan2006],
  Section 1.2 (Definition 1.7), Section 2.1 (Definition 2.1), and Section 7.1 (Lemma 7.1);
  checked against ECCC TR01-080 (pp. 4, 6, 19–20)
* [I. Kerenidis, R. de Wolf, *Exponential lower bound for 2-query locally decodable codes via a
  quantum argument*][KerenidisDeWolf2004], Appendix B, Lemma 3 (p. 16 of arXiv:quant-ph/0208062v2)
* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
-/

public section

open scoped ENNReal BigOperators

namespace Cslib.Crypto.Protocols.PIR

open Code OracleComp ProbOracleComp Probability

section SmoothCode

variable {ι S R Q A : Type}

/-- Replication count `max 1 ⌈p₀(s, q) · (|S| · |Q|)⌉₊` of server-query pair `sq = (s, q)` in the
GKST smooth-code construction with reference index `i₀`
[GKST, Section 7.1, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]. Clamping below at `1`
matches the proof's low-probability case (`p_j ≤ 1 / l` gets one copy even when `p_j = 0`) without
increasing the `(k + 1) k |Q|` length bound. -/
@[expose] def smoothCopies (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (sq : S × Q) : ℕ :=
  max 1 ⌈ProbComp.evalRat (P.serverQuery sq.1 i₀) sq.2 * (Fintype.card S * Fintype.card Q : ℚ)⌉₊

theorem smoothCopies_eq (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (sq : S × Q) :
    smoothCopies P i₀ sq =
      max 1
        ⌈ProbComp.evalRat (P.serverQuery sq.1 i₀) sq.2 * (Fintype.card S * Fintype.card Q : ℚ)⌉₊ :=
  rfl

theorem smoothCopies_pos (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (sq : S × Q) : 0 < smoothCopies P i₀ sq :=
  lt_max_of_lt_left Nat.zero_lt_one

/-- Codeword positions of the GKST smooth code: pairs `⟨(s, q), idx⟩` with `idx` ranging over the
`smoothCopies P i₀ (s, q)` copies of `(s, q)`. -/
abbrev SmoothPos (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q] (i₀ : ι) : Type :=
  Σ sq : S × Q, Fin (smoothCopies P i₀ sq)

/-- The GKST smooth code `C : (ι → Bool) → SmoothPos P i₀ → A`: every copy of `(s, q)` stores
`P.answer s x q`
[GKST, Section 7.1, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]. -/
def smoothCode (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (x : ι → Bool) : SmoothPos P i₀ → A
  | ⟨(s, q), _⟩ => P.answer s x q

@[simp] theorem smoothCode_apply (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (x : ι → Bool) (sq : S × Q) (idx : Fin (smoothCopies P i₀ sq)) :
    smoothCode P i₀ x ⟨sq, idx⟩ = P.answer sq.1 x sq.2 := by
  rcases sq with ⟨s, q⟩
  rfl

/-- **Codeword length bound** ([GKST, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]): the
replicated table has at most `(|S| + 1) · |S| · |Q|` positions. -/
theorem card_smoothPos_le (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) :
    Fintype.card (SmoothPos P i₀) ≤ (Fintype.card S + 1) * Fintype.card S * Fintype.card Q := by
  classical
  set l : ℕ := Fintype.card S * Fintype.card Q
  have hterm (sq : S × Q) :
      (smoothCopies P i₀ sq : ℝ) ≤
        1 + (ProbComp.eval (P.serverQuery sq.1 i₀) sq.2).toReal * l := by
    set r : ℚ := ProbComp.evalRat (P.serverQuery sq.1 i₀) sq.2 * (l : ℚ)
    have hr0 : 0 ≤ r := mul_nonneg (ProbComp.evalRat_nonneg _ _) (Nat.cast_nonneg l)
    have hrR : (r : ℝ) = (ProbComp.eval (P.serverQuery sq.1 i₀) sq.2).toReal * l := by
      simp [r, l, ProbComp.coe_evalRat_eq_toReal_eval]
    have h0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hsc : smoothCopies P i₀ sq = max 1 ⌈r⌉₊ := by simp [smoothCopies, r, l]
    rw [hsc, ← hrR]
    rcases le_or_gt ⌈r⌉₊ 1 with hle | hgt
    · rw [Nat.max_eq_left hle, Nat.cast_one]
      linarith
    · rw [Nat.max_eq_right hgt.le]
      have hlt : (⌈r⌉₊ : ℚ) < r + 1 := Nat.ceil_lt_add_one hr0
      have hltR : ((⌈r⌉₊ : ℕ) : ℝ) < (r : ℝ) + 1 := by exact_mod_cast hlt
      linarith
  have hsum_all :
      ∑ sq : S × Q, (ProbComp.eval (P.serverQuery sq.1 i₀) sq.2).toReal = Fintype.card S := by
    rw [Fintype.sum_prod_type]
    simp only [PMF.sum_toReal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hreal :
      (Fintype.card (SmoothPos P i₀) : ℝ) ≤
        ((Fintype.card S + 1) * Fintype.card S * Fintype.card Q : ℕ) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_sum]
    calc ∑ sq : S × Q, (smoothCopies P i₀ sq : ℝ)
        ≤ ∑ sq : S × Q, (1 + (ProbComp.eval (P.serverQuery sq.1 i₀) sq.2).toReal * l) :=
          Finset.sum_le_sum fun sq _ => hterm sq
      _ = (Fintype.card (S × Q) : ℝ) +
            (∑ sq : S × Q, (ProbComp.eval (P.serverQuery sq.1 i₀) sq.2).toReal) * l := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            ← Finset.sum_mul]
      _ = ((Fintype.card S + 1) * Fintype.card S * Fintype.card Q : ℕ) := by
          rw [Fintype.card_prod, hsum_all]
          push_cast [l]
          ring
  exact_mod_cast hreal

/-- Two-server specialization of `card_smoothPos_le`: `m ≤ 6 · |Q|`
([GKST, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006];
[Kerenidis and de Wolf, Appendix B, Lemma 3][KerenidisDeWolf2004]). -/
theorem card_smoothPos_le_six_mul (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (hS : Fintype.card S = 2) (i₀ : ι) :
    Fintype.card (SmoothPos P i₀) ≤ 6 * Fintype.card Q := by
  simpa [hS] using card_smoothPos_le P i₀

/-! ### Linearity preservation (GKST Lemma 7.1, item 1) -/

theorem smoothCode_zero (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q] [Zero A]
    (hzero : ∀ s q, P.answer s 0 q = 0) (i₀ : ι) :
    smoothCode P i₀ 0 = 0 :=
  funext fun ⟨(s, q), _⟩ => hzero s q

theorem smoothCode_add (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q] [Add A]
    (hadd : ∀ s x y q, P.answer s (x + y) q = P.answer s x q + P.answer s y q)
    (i₀ : ι) (x y : ι → Bool) :
    smoothCode P i₀ (x + y) = smoothCode P i₀ x + smoothCode P i₀ y :=
  funext fun ⟨(s, q), _⟩ => hadd s x y q

/-- **Linearity preservation** ([GKST, Lemma 7.1, item 1][GoldreichKarloffSchulmanTrevisan2006]):
when each server's answer map `x ↦ P.answer s x q` is an additive homomorphism (for instance, XOR
linear combinations of database bits over `GF(2)`), `smoothCode P i₀` is an `AddMonoidHom`. -/
def smoothCodeAddHom (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    [AddZeroClass A] (hzero : ∀ s q, P.answer s 0 q = 0)
    (hadd : ∀ s x y q, P.answer s (x + y) q = P.answer s x q + P.answer s y q) (i₀ : ι) :
    (ι → Bool) →+ (SmoothPos P i₀ → A) where
  toFun := smoothCode P i₀
  map_zero' := smoothCode_zero P hzero i₀
  map_add' := smoothCode_add P hadd i₀

end SmoothCode

/-! ### The GKST smooth decoder -/

section SmoothDecoder

variable {ι S R Q A : Type}

/-- Upfront random coins sampled by `smoothDecoder` before making any oracle query. -/
structure SmoothCoins (R : Type) (k : ℕ) (Pos : Type) where
  /-- Client private state from `P.query i`. -/
  state : R
  /-- Uniform fallback bit returned when any server slot enters failure mode. -/
  guess : Bool
  /-- Per-server optional codeword position (`none` signals failure mode on that slot). -/
  slots : Fin k → Option Pos

/-- Acceptance probability ratio `p₀(s, q) / pᵢ(s, q)` (clamped to `1` when `pᵢ ≤ p₀`) used by
the GKST statistical-privacy rejection step
[GKST, Section 7.1, Lemma 7.1, p. 20][GoldreichKarloffSchulmanTrevisan2006]. -/
@[expose] def smoothKeepRatio (P : Scheme ι S R Q A) [DecidableEq Q] (i₀ i : ι)
    (s : S) (q : Q) : ℚ :=
  let p₀ := ProbComp.evalRat (P.serverQuery s i₀) q
  let pᵢ := ProbComp.evalRat (P.serverQuery s i) q
  if pᵢ ≤ p₀ then 1 else p₀ / pᵢ

theorem smoothKeepRatio_eq (P : Scheme ι S R Q A) [DecidableEq Q] (i₀ i : ι)
    (s : S) (q : Q) :
    smoothKeepRatio P i₀ i s q =
      if ProbComp.evalRat (P.serverQuery s i) q ≤ ProbComp.evalRat (P.serverQuery s i₀) q then 1
      else ProbComp.evalRat (P.serverQuery s i₀) q / ProbComp.evalRat (P.serverQuery s i) q :=
  rfl

/-- Per-server coin draw for `smoothDecoder`: keep `(s, q)` with probability
`smoothKeepRatio P i₀ i s q`, and when kept pick a uniform replica of `(s, q)`. -/
private noncomputable def smoothSlotCoins (P : Scheme ι S R Q A) [Fintype S] [Fintype Q]
    [DecidableEq Q] (i₀ i : ι) (s : S) (q : Q) : ProbComp (Option (SmoothPos P i₀)) := do
  let keep ← ProbComp.bernoulliRat (smoothKeepRatio P i₀ i s q)
  if keep then
    let _ : Nonempty (Fin (smoothCopies P i₀ (s, q))) := ⟨⟨0, smoothCopies_pos P i₀ (s, q)⟩⟩
    let idx ← ProbComp.uniform (Fin (smoothCopies P i₀ (s, q)))
    pure (some ⟨(s, q), idx⟩)
  else
    pure none

/-- Upfront private-coin draw of the GKST smooth decoder before making any oracle queries. -/
noncomputable def smoothCoins (P : Scheme ι S R Q A) [Fintype S] [Fintype Q]
    [DecidableEq Q] (i₀ i : ι) :
    ProbComp (SmoothCoins R (Fintype.card S) (SmoothPos P i₀)) := do
  let eS := Fintype.equivFin S
  let rq ← P.query i
  let guess ← ProbComp.uniform Bool
  let slots ← OracleComp.pi fun k : Fin (Fintype.card S) =>
    smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))
  pure ⟨rq.1, guess, slots⟩

/-- **GKST smooth decoder** ([GKST, Section 7.1, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]):
sample `st ← smoothCoins P i₀ i`; if every server slot survived (`∀ idx, (st.slots idx).isSome`),
read all `|S|` selected codeword positions non-adaptively via `Code.readAll` and run
`P.reconstruct i st.state`; otherwise output the uniform fallback bit `st.guess` without querying
the codeword. -/
noncomputable def smoothDecoder (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) : LocalDecoder ι (SmoothPos P i₀) A := fun i => do
  let st ← sample (smoothCoins P i₀ i)
  if h : ∀ idx, (st.slots idx).isSome then
    let ans ← readAll fun idx => (st.slots idx).get (h idx)
    pure (P.reconstruct i st.state fun s => ans (Fintype.equivFin S s))
  else
    pure st.guess

theorem isQueryBounded_smoothDecoder (P : Scheme ι S R Q A) [Fintype S] [Fintype Q] [DecidableEq Q]
    (i₀ : ι) (i : ι) : (smoothDecoder P i₀ i).IsQueryBounded (Fintype.card S) := by
  refine ((IsQueryBounded.sample (spec := fun _ : SmoothPos P i₀ => A)
    (smoothCoins P i₀ i)).bind fun st => ?_).mono (Nat.zero_add _).le
  split_ifs with h
  · refine ((isQueryBounded_readAll (Γ := A) fun idx => (st.slots idx).get (h idx)).bind
      fun _ => IsCostBounded.pure _ 0).mono (Nat.add_zero _).le
  · exact (IsCostBounded.pure _ 0).mono (Nat.zero_le _)

theorem hasObliviousReads_smoothDecoder (P : Scheme ι S R Q A) [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (i₀ : ι) (i : ι) :
    HasObliviousReads (smoothDecoder P i₀ i) := by
  refine hasObliviousReads_iff.mpr fun y y' j => ?_
  simp only [smoothDecoder, expectedReads_bind, expectedReads_sample, zero_add, decodeLaw_sample]
  refine tsum_congr fun st => congrArg _ ?_
  split_ifs with h
  · simp only [expectedReads_bind, expectedReads_readAll, expectedReads_pure, mul_zero, tsum_zero,
      add_zero]
  · simp

private theorem toReal_eval_smoothSlotCoins_some (P : Scheme ι S R Q A) [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (i₀ i : ι) (s : S) (q : Q) (j : SmoothPos P i₀) :
    (ProbComp.eval (smoothSlotCoins P i₀ i s q) (some j)).toReal =
      if j.1 = (s, q) then
        (ProbComp.eval (ProbComp.bernoulliRat (smoothKeepRatio P i₀ i s q)) true).toReal /
          smoothCopies P i₀ (s, q)
      else 0 := by
  let _ : Nonempty (Fin (smoothCopies P i₀ (s, q))) := ⟨⟨0, smoothCopies_pos P i₀ (s, q)⟩⟩
  let embed : Fin (smoothCopies P i₀ (s, q)) → Option (SmoothPos P i₀) :=
    fun u => some ⟨(s, q), u⟩
  rw [smoothSlotCoins, ProbComp.eval_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.pure_apply, reduceCtorEq, mul_zero, add_zero]
  change (_ * (((PMF.uniformOfFintype (Fin (smoothCopies P i₀ (s, q)))).map embed)
    (some j))).toReal = _
  rw [ENNReal.toReal_mul]
  rcases j with ⟨sq', idx'⟩
  by_cases hsq : sq' = (s, q)
  · subst hsq
    have hinj : Function.Injective embed := (Option.some_injective _).comp sigma_mk_injective
    rw [Probability.PMF.map_apply_of_injective _ hinj idx']
    simp [PMF.uniformOfFintype_apply, div_eq_mul_inv]
  · rw [ite_eq_right hsq]
    have hz : ((PMF.uniformOfFintype (Fin (smoothCopies P i₀ (s, q)))).map embed)
        (some ⟨sq', idx'⟩) = 0 := by
      rw [PMF.apply_eq_zero_iff, PMF.support_map]
      rintro ⟨u, _, hu⟩
      exact hsq (congrArg Sigma.fst (Option.some.inj hu)).symm
    rw [hz, ENNReal.toReal_zero, mul_zero]

private theorem eval_smoothSlotCoins_none (P : Scheme ι S R Q A) [Fintype S]
    [Fintype Q] [DecidableEq Q] (i₀ i : ι) (s : S) (q : Q) :
    ProbComp.eval (smoothSlotCoins P i₀ i s q) none =
      ProbComp.eval (ProbComp.bernoulliRat (smoothKeepRatio P i₀ i s q)) false := by
  let _ : Nonempty (Fin (smoothCopies P i₀ (s, q))) := ⟨⟨0, smoothCopies_pos P i₀ (s, q)⟩⟩
  rw [smoothSlotCoins, ProbComp.eval_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.pure_apply, mul_one]
  change _ * (((PMF.uniformOfFintype (Fin (smoothCopies P i₀ (s, q)))).map
    fun idx => (some ⟨(s, q), idx⟩ : Option (SmoothPos P i₀))) none) + _ = _
  have hz : ((PMF.uniformOfFintype (Fin (smoothCopies P i₀ (s, q)))).map
      fun idx => (some ⟨(s, q), idx⟩ : Option (SmoothPos P i₀))) none = 0 := by
    rw [PMF.apply_eq_zero_iff, PMF.support_map]
    simp
  rw [hz, mul_zero, zero_add]

private theorem mul_keepProb_eq_min (P : Scheme ι S R Q A) [DecidableEq Q]
    (i₀ i : ι) (s : S) (q : Q) :
    (ProbComp.eval (P.serverQuery s i) q).toReal *
        (ProbComp.eval (ProbComp.bernoulliRat (smoothKeepRatio P i₀ i s q)) true).toReal =
      min (ProbComp.eval (P.serverQuery s i₀) q).toReal
        (ProbComp.eval (P.serverQuery s i) q).toReal := by
  set p₀ : ℚ := ProbComp.evalRat (P.serverQuery s i₀) q
  set pᵢ : ℚ := ProbComp.evalRat (P.serverQuery s i) q
  have hp₀R : (p₀ : ℝ) = (ProbComp.eval (P.serverQuery s i₀) q).toReal :=
    ProbComp.coe_evalRat_eq_toReal_eval _ _
  have hpᵢR : (pᵢ : ℝ) = (ProbComp.eval (P.serverQuery s i) q).toReal :=
    ProbComp.coe_evalRat_eq_toReal_eval _ _
  rw [← hp₀R, ← hpᵢR, smoothKeepRatio]
  change (pᵢ : ℝ) * (ProbComp.eval (ProbComp.bernoulliRat (if pᵢ ≤ p₀ then 1 else p₀ / pᵢ))
    true).toReal = min (p₀ : ℝ) (pᵢ : ℝ)
  by_cases hle : pᵢ ≤ p₀
  · rw [ite_eq_left hle, ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc zero_le_one le_rfl,
      Rat.cast_one, mul_one, min_eq_right (by exact_mod_cast hle)]
  · rw [ite_eq_right hle]
    have hlt : p₀ < pᵢ := lt_of_not_ge hle
    have hp₀_nonneg : 0 ≤ p₀ := ProbComp.evalRat_nonneg _ _
    have hpᵢ_pos : 0 < pᵢ := hp₀_nonneg.trans_lt hlt
    have hdiv0 : 0 ≤ p₀ / pᵢ := div_nonneg hp₀_nonneg hpᵢ_pos.le
    have hdiv1 : p₀ / pᵢ ≤ 1 := (div_le_one hpᵢ_pos).mpr hlt.le
    rw [ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc hdiv0 hdiv1, Rat.cast_div]
    have hpᵢR_ne : (pᵢ : ℝ) ≠ 0 := by exact_mod_cast hpᵢ_pos.ne'
    rw [mul_div_cancel₀ _ hpᵢR_ne, min_eq_left (by exact_mod_cast hlt.le)]

/-- **Smoothness of the GKST decoder**: against every received word `y` (obliviously), each
position `j : SmoothPos P i₀` is read at most `(|S| + 1) / |SmoothPos P i₀|` times in
expectation. -/
theorem expectedReads_smoothDecoder_le (P : Scheme ι S R Q A) [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (i₀ : ι) (y : SmoothPos P i₀ → A) (i : ι)
    (j : SmoothPos P i₀) :
    (expectedReads (smoothDecoder P i₀ i) y j).toReal ≤
      (Fintype.card S + 1 : ℝ) / Fintype.card (SmoothPos P i₀) := by
  let eS := Fintype.equivFin S
  have hexp :
      expectedReads (smoothDecoder P i₀ i) y j ≤
        ∑ k : Fin (Fintype.card S),
          ((ProbComp.eval (smoothCoins P i₀ i)).map (fun st => st.slots k)) (some j) := by
    simp only [smoothDecoder, expectedReads_bind, expectedReads_sample, zero_add, decodeLaw_sample]
    have hst (st : SmoothCoins R (Fintype.card S) (SmoothPos P i₀)) :
        expectedReads
            (if h : ∀ idx, (st.slots idx).isSome then do
              let ans ← readAll fun idx => (st.slots idx).get (h idx)
              pure (P.reconstruct i st.state fun s => ans (eS s))
            else pure st.guess) y j ≤
          ∑ k : Fin (Fintype.card S), if st.slots k = some j then 1 else 0 := by
      split_ifs with h
      · simp only [expectedReads_bind, expectedReads_readAll, expectedReads_pure, mul_zero,
          tsum_zero, add_zero]
        refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
        have hk : (st.slots k).get (h k) = j ↔ st.slots k = some j := by
          conv_rhs => rw [← Option.some_get (h k), Option.some.injEq]
        simp [hk]
      · simp only [expectedReads_pure]
        exact zero_le
    calc ∑' st, ProbComp.eval (smoothCoins P i₀ i) st *
            expectedReads
              (if h : ∀ idx, (st.slots idx).isSome then do
                let ans ← readAll fun idx => (st.slots idx).get (h idx)
                pure (P.reconstruct i st.state fun s => ans (eS s))
              else pure st.guess) y j
        ≤ ∑' st, ProbComp.eval (smoothCoins P i₀ i) st *
            ∑ k : Fin (Fintype.card S), if st.slots k = some j then 1 else 0 :=
          tsum_le_tsum fun st => mul_le_mul_right (hst st) _
      _ = ∑ k : Fin (Fintype.card S),
            ((ProbComp.eval (smoothCoins P i₀ i)).map (fun st => st.slots k)) (some j) := by
          simp only [Finset.mul_sum]
          rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [PMF.map_apply]
          refine tsum_congr fun st => ?_
          by_cases h : st.slots k = some j <;> simp [h, eq_comm]
  have hslot_law (k : Fin (Fintype.card S)) :
      (ProbComp.eval (smoothCoins P i₀ i)).map (fun st => st.slots k) =
        (ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
          (fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) := by
    rw [smoothCoins, P.eval_serverQuery]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map, PMF.bind_map]
    refine congrArg (ProbComp.eval (P.query i)).bind (funext fun rq => ?_)
    have hconst : ∀ g : Bool,
        ((ProbComp.eval (OracleComp.pi fun idx : Fin (Fintype.card S) =>
          smoothSlotCoins P i₀ i (eS.symm idx) (rq.2 (eS.symm idx)))).bind
            fun slots => PMF.pure (slots k)) =
          ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) := by
      intro _
      change ((ProbComp.eval (OracleComp.pi fun idx : Fin (Fintype.card S) =>
        smoothSlotCoins P i₀ i (eS.symm idx) (rq.2 (eS.symm idx)))).map (fun slots => slots k)) = _
      rw [ProbComp.eval_pi, Probability.PMF.pi_map_eval]
    rw [congrArg (ProbComp.eval (ProbComp.uniform Bool)).bind (funext hconst), PMF.bind_const]
    rfl
  rcases j with ⟨⟨s₀, q₀⟩, idx₀⟩
  have hS_pos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s₀⟩
  have hQ_pos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q₀⟩
  set l : ℕ := Fintype.card S * Fintype.card Q
  have hl_pos : (0 : ℝ) < l := by exact_mod_cast Nat.mul_pos hS_pos hQ_pos
  have hm_pos : (0 : ℝ) < Fintype.card (SmoothPos P i₀) := by
    have hne : Nonempty (SmoothPos P i₀) := ⟨⟨(s₀, q₀), idx₀⟩⟩
    exact_mod_cast Fintype.card_pos
  have hsum_ne_top :
      (∑ k : Fin (Fintype.card S),
        ((ProbComp.eval (smoothCoins P i₀ i)).map (fun st => st.slots k))
          (some ⟨(s₀, q₀), idx₀⟩)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => PMF.apply_ne_top _ _
  have hexp_real := ENNReal.toReal_mono hsum_ne_top hexp
  rw [ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ _] at hexp_real
  have hk_val (k : Fin (Fintype.card S)) :
      (((ProbComp.eval (smoothCoins P i₀ i)).map (fun st => st.slots k))
        (some ⟨(s₀, q₀), idx₀⟩)).toReal =
        if k = eS s₀ then
          min (ProbComp.eval (P.serverQuery s₀ i₀) q₀).toReal
            (ProbComp.eval (P.serverQuery s₀ i) q₀).toReal / smoothCopies P i₀ (s₀, q₀)
        else 0 := by
    rw [hslot_law k, PMF.bind_apply_toReal]
    simp only [toReal_eval_smoothSlotCoins_some]
    by_cases hk : k = eS s₀
    · subst hk
      simp only [Equiv.symm_apply_apply, ↓reduceIte]
      rw [Finset.sum_eq_single q₀]
      · simp only [↓reduceIte, ← mul_div_assoc, mul_keepProb_eq_min]
      · intro q _ hq
        have hne : ((s₀, q₀) : S × Q) ≠ (s₀, q) := fun h => hq (Prod.mk.inj h).2.symm
        simp [hne]
      · intro hmem
        exact (hmem (Finset.mem_univ q₀)).elim
    · rw [ite_eq_right hk]
      refine Finset.sum_eq_zero fun q _ => ?_
      have hne : ((s₀, q₀) : S × Q) ≠ (eS.symm k, q) := by
        intro h
        exact hk ((Equiv.eq_symm_apply eS).mp (Prod.mk.inj h).1).symm
      simp [hne]
  simp only [hk_val, Fintype.sum_ite_eq'] at hexp_real
  set p₀ : ℝ := (ProbComp.eval (P.serverQuery s₀ i₀) q₀).toReal
  set pᵢ : ℝ := (ProbComp.eval (P.serverQuery s₀ i) q₀).toReal
  have hn₀_pos : (0 : ℝ) < smoothCopies P i₀ (s₀, q₀) := by
    exact_mod_cast smoothCopies_pos P i₀ (s₀, q₀)
  have hceil : p₀ * l ≤ smoothCopies P i₀ (s₀, q₀) := by
    have hp₀_rat : (ProbComp.evalRat (P.serverQuery s₀ i₀) q₀ : ℝ) = p₀ :=
      ProbComp.coe_evalRat_eq_toReal_eval _ _
    set rq : ℚ := ProbComp.evalRat (P.serverQuery s₀ i₀) q₀ * (l : ℚ)
    have hsc : smoothCopies P i₀ (s₀, q₀) = max 1 ⌈rq⌉₊ := by simp [smoothCopies, rq, l]
    have h1 : rq ≤ (⌈rq⌉₊ : ℚ) := Nat.le_ceil rq
    have h2 : (⌈rq⌉₊ : ℚ) ≤ (max 1 ⌈rq⌉₊ : ℕ) := by exact_mod_cast le_max_right 1 ⌈rq⌉₊
    have hle_q : rq ≤ (smoothCopies P i₀ (s₀, q₀) : ℚ) := by rw [hsc]; exact h1.trans h2
    have hle_r : (rq : ℝ) ≤ (smoothCopies P i₀ (s₀, q₀) : ℝ) := by exact_mod_cast hle_q
    simpa [rq, hp₀_rat, l] using hle_r
  have hmin_le : min p₀ pᵢ * l ≤ smoothCopies P i₀ (s₀, q₀) :=
    (mul_le_mul_of_nonneg_right (min_le_left p₀ pᵢ) hl_pos.le).trans hceil
  have hstep1 : min p₀ pᵢ / smoothCopies P i₀ (s₀, q₀) ≤ 1 / l := by
    rw [div_le_div_iff₀ hn₀_pos hl_pos, one_mul]
    exact hmin_le
  have hm_le : (Fintype.card (SmoothPos P i₀) : ℝ) ≤ (Fintype.card S + 1 : ℝ) * l := by
    have h := card_smoothPos_le P i₀
    have hR : (Fintype.card (SmoothPos P i₀) : ℝ) ≤
        ((Fintype.card S + 1) * Fintype.card S * Fintype.card Q : ℕ) := by exact_mod_cast h
    simpa [l, mul_assoc] using hR
  have hstep2 : (1 : ℝ) / l ≤ (Fintype.card S + 1 : ℝ) / Fintype.card (SmoothPos P i₀) := by
    rw [div_le_div_iff₀ hl_pos hm_pos, one_mul]
    exact hm_le
  exact hexp_real.trans (hstep1.trans hstep2)

private theorem decodeLaw_smoothDecoder_branch (P : Scheme ι S R Q A) [Fintype S]
    [Fintype Q] [DecidableEq Q] (i₀ : ι) (x : ι → Bool) (i : ι) (r : R) (g : Bool)
    (slots : Fin (Fintype.card S) → Option (SmoothPos P i₀)) :
    decodeLaw
        (if h : ∀ idx, (slots idx).isSome then do
          let ans ← readAll fun idx => (slots idx).get (h idx)
          pure (P.reconstruct i r fun s => ans (Fintype.equivFin S s))
        else pure g) (smoothCode P i₀ x) =
      if h : ∀ idx, (slots idx).isSome then
        PMF.pure (P.reconstruct i r fun s =>
          smoothCode P i₀ x ((slots (Fintype.equivFin S s)).get (h (Fintype.equivFin S s))))
      else
        PMF.pure g := by
  split_ifs with h
  · simp [decodeLaw_readAll, Function.comp_def]
  · simp

/-- **Recovery bound of the GKST decoder**: when each server's query distributions are `δ`-close
in total variation (`CloseTo`) to those at the reference index `i₀` (in particular under pairwise
`δ`-closeness) and `P` recovers `x i` with probability at least `1 / 2 + ε`, `smoothDecoder P i₀`
recovers `x i` from `smoothCode P i₀ x` with probability at least `1 / 2 + ε - |S| · δ / 2`. -/
theorem toReal_decodeLaw_smoothDecoder_ge (P : Scheme ι S R Q A) [Fintype S]
    [Fintype Q] [DecidableEq Q] (i₀ : ι) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hpriv : ∀ s i,
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i₀))
        (ENNReal.ofReal δ))
    (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal)
    (x : ι → Bool) (i : ι) :
    1 / 2 + (ε - Fintype.card S * δ / 2) ≤
      (decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) (x i)).toReal := by
  classical
  let eS := Fintype.equivFin S
  let slotDist (rq : R × (S → Q)) :
      PMF (Fin (Fintype.card S) → Option (SmoothPos P i₀)) :=
    ProbComp.eval (OracleComp.pi fun k : Fin (Fintype.card S) =>
      smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k)))
  have hlaw :
      decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) (x i) =
        ∑' rq : R × (S → Q), ProbComp.eval (P.query i) rq *
          ∑' slots : Fin (Fintype.card S) → Option (SmoothPos P i₀), slotDist rq slots *
            if h : ∀ k, (slots k).isSome then
              if P.reconstruct i rq.1
                  (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i then 1 else 0
            else (2 : ℝ≥0∞)⁻¹ := by
    have hpmf :
        decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) =
          (ProbComp.eval (P.query i)).bind fun rq =>
            (PMF.uniformOfFintype Bool).bind fun g =>
              (slotDist rq).bind fun slots =>
                if h : ∀ idx, (slots idx).isSome then
                  PMF.pure (P.reconstruct i rq.1
                    fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s))))
                else
                  PMF.pure g := by
      simp only [smoothDecoder, smoothCoins, decodeLaw_bind, decodeLaw_sample,
        ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind,
        PMF.pure_bind, decodeLaw_smoothDecoder_branch]
      rfl
    rw [hpmf, PMF.bind_apply]
    refine tsum_congr fun rq => ?_
    congr 1
    rw [PMF.bind_comm, PMF.bind_apply]
    refine tsum_congr fun slots => ?_
    congr 1
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    by_cases h : ∀ k, (slots k).isSome
    · simp only [dite_eq_left h]
      by_cases hb :
          P.reconstruct i rq.1
            (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i
      · simp only [hb, ↓reduceIte, PMF.pure_apply, mul_one]
        exact ENNReal.inv_two_add_inv_two
      · have hne : x i ≠ P.reconstruct i rq.1
            (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) := Ne.symm hb
        simp [hb, hne, PMF.pure_apply]
    · simp only [dite_eq_right h]
      rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi <;> simp [hxi, PMF.pure_apply]
  -- Pointwise lower bound on supported `slots` without subtraction in `ℝ≥0∞`:
  have hpt (rq : R × (S → Q))
      (slots : Fin (Fintype.card S) → Option (SmoothPos P i₀))
      (hslots : slots ∈ (slotDist rq).support) :
      (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then (1 : ℝ≥0∞) else 0) ≤
        (if h : ∀ k, (slots k).isSome then
          if P.reconstruct i rq.1
              (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i then 1 else 0
        else (2 : ℝ≥0∞)⁻¹) +
          (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S), if slots k = none then 1 else 0 := by
    rw [ProbComp.mem_support_pi_iff] at hslots
    by_cases hall : ∀ k, (slots k).isSome
    · rw [dite_eq_left hall]
      have hval (k : Fin (Fintype.card S)) :
          smoothCode P i₀ x ((slots k).get (hall k)) =
            P.answer (eS.symm k) x (rq.2 (eS.symm k)) := by
        have hk := hslots k
        set opt := slots k
        have hopt : opt = some (opt.get (hall k)) := (Option.some_get (hall k)).symm
        rw [hopt] at hk
        have hpos : (ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k)))
            (some (opt.get (hall k)))).toReal ≠ 0 := by
          intro hz
          have h0 : ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k)))
              (some (opt.get (hall k))) = 0 := by
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), hz, ENNReal.ofReal_zero]
          exact (PMF.mem_support_iff _ _).mp hk h0
        rw [toReal_eval_smoothSlotCoins_some] at hpos
        rcases pos : opt.get (hall k) with ⟨⟨s', q'⟩, idx'⟩
        rw [pos] at hpos
        have hsq : (s', q') = (eS.symm k, rq.2 (eS.symm k)) := by
          by_contra hne
          rw [ite_eq_right hne] at hpos
          exact hpos rfl
        rcases Prod.mk.inj hsq with ⟨rfl, rfl⟩
        rfl
      have hrec_eq :
          (fun s : S => smoothCode P i₀ x ((slots (eS s)).get (hall (eS s)))) =
            fun s : S => P.answer s x (rq.2 s) := by
        funext s
        rw [hval (eS s), Equiv.symm_apply_apply]
      rw [hrec_eq]
      exact le_self_add
    · rw [dite_eq_right hall]
      push Not at hall
      obtain ⟨k₀, hk₀⟩ := hall
      have hnone : slots k₀ = none := Option.not_isSome_iff_eq_none.mp (by simpa using hk₀)
      have hsum_ge : (1 : ℝ≥0∞) ≤ ∑ k : Fin (Fintype.card S), if slots k = none then 1 else 0 := by
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k₀))
        simp [hnone]
      calc (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then (1 : ℝ≥0∞) else 0)
          ≤ 1 := by split_ifs <;> simp
        _ = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * 1 := by simp [ENNReal.inv_two_add_inv_two]
        _ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ *
              ∑ k : Fin (Fintype.card S), if slots k = none then 1 else 0 := by
            gcongr
  -- Sum the `ℝ≥0∞` inequality over `slots` and `rq`:
  have hpir_ennreal :
      ProbComp.eval (P.run x i) (x i) ≤
        decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) (x i) +
          (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S),
            ((ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
              fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) none := by
    have hpir_lhs :
        ProbComp.eval (P.run x i) (x i) =
          ∑' rq : R × (S → Q), ProbComp.eval (P.query i) rq *
            if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then 1 else 0 := by
      rw [P.eval_run, PMF.map_apply]
      refine tsum_congr fun rq => ?_
      by_cases h : P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i
      · simp [h]
      · have h' : x i ≠ P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) := Ne.symm h
        simp [h, h']
    rw [hpir_lhs, hlaw]
    have hinner (rq : R × (S → Q)) :
        (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then (1 : ℝ≥0∞) else 0) ≤
          (∑' slots, slotDist rq slots *
            if h : ∀ k, (slots k).isSome then
              if P.reconstruct i rq.1
                  (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i then 1 else 0
            else (2 : ℝ≥0∞)⁻¹) +
          (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S),
            ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) none := by
      have h1 :
          (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then (1 : ℝ≥0∞) else 0) =
            ∑' slots, slotDist rq slots *
              (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then 1 else 0) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      have hpt_mul (slots : Fin (Fintype.card S) → Option (SmoothPos P i₀)) :
          slotDist rq slots *
              (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then 1 else 0) ≤
            slotDist rq slots *
              ((if h : ∀ k, (slots k).isSome then
                  if P.reconstruct i rq.1
                      (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i then
                    1
                  else 0
                else (2 : ℝ≥0∞)⁻¹) +
                (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S), if slots k = none then 1 else 0) := by
        by_cases hs : slots ∈ (slotDist rq).support
        · exact mul_le_mul_right (hpt rq slots hs) _
        · have hz : slotDist rq slots = 0 := (PMF.apply_eq_zero_iff _ _).mpr hs
          simp [hz]
      rw [h1]
      refine (tsum_le_tsum hpt_mul).trans ?_
      simp only [mul_add, tsum_add]
      refine add_le_add le_rfl ?_
      have hrw :
          (∑' slots, slotDist rq slots *
            ((2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S), if slots k = none then (1 : ℝ≥0∞) else 0)) =
            (2 : ℝ≥0∞)⁻¹ * ∑' slots, ∑ k : Fin (Fintype.card S),
              slotDist rq slots * if slots k = none then (1 : ℝ≥0∞) else 0 := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun slots => ?_
        rw [← mul_assoc, mul_comm (slotDist rq slots) (2 : ℝ≥0∞)⁻¹, mul_assoc, Finset.mul_sum]
      rw [hrw, Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
      refine le_of_eq (congrArg ((2 : ℝ≥0∞)⁻¹ * ·) (Finset.sum_congr rfl fun k _ => ?_))
      have hproj :
          ((slotDist rq).map (fun slots => slots k)) none =
            ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) none := by
        simp only [slotDist, ProbComp.eval_pi, Probability.PMF.pi_map_eval]
      rw [← hproj, PMF.map_apply]
      refine tsum_congr fun slots => ?_
      by_cases hn : slots k = none
      · simp [hn]
      · have hn' : none ≠ slots k := Ne.symm hn
        simp [hn, hn']
    calc ∑' rq, ProbComp.eval (P.query i) rq *
            (if P.reconstruct i rq.1 (fun s => P.answer s x (rq.2 s)) = x i then 1 else 0)
        ≤ ∑' rq, ProbComp.eval (P.query i) rq *
            ((∑' slots, slotDist rq slots *
              if h : ∀ k, (slots k).isSome then
                if P.reconstruct i rq.1
                    (fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s)))) = x i then 1 else 0
              else (2 : ℝ≥0∞)⁻¹) +
            (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S),
              ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) none) :=
          tsum_le_tsum fun rq => mul_le_mul_right (hinner rq) _
      _ = _ := by
          simp only [mul_add, tsum_add]
          congr 1
          have hrw2 :
              (∑' rq, ProbComp.eval (P.query i) rq *
                ((2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S),
                  ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) none)) =
                (2 : ℝ≥0∞)⁻¹ * ∑' rq, ∑ k : Fin (Fintype.card S),
                  ProbComp.eval (P.query i) rq *
                    ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k))) none := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun rq => ?_
            rw [← mul_assoc, mul_comm (ProbComp.eval (P.query i) rq) (2 : ℝ≥0∞)⁻¹, mul_assoc,
              Finset.mul_sum]
          rw [hrw2, Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [P.eval_serverQuery, PMF.bind_map, PMF.bind_apply]
          rfl
  -- Bound each server's failure probability by `δ` via `CloseTo`:
  have hfail_le (k : Fin (Fintype.card S)) :
      (((ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
        fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) none).toReal ≤ δ := by
    set s := eS.symm k
    rw [PMF.bind_apply_toReal]
    simp only [eval_smoothSlotCoins_none]
    have hterm_eq (q : Q) :
        (ProbComp.eval (P.serverQuery s i) q).toReal *
            (ProbComp.eval (ProbComp.bernoulliRat (smoothKeepRatio P i₀ i s q)) false).toReal =
          if (ProbComp.eval (P.serverQuery s i₀) q).toReal <
              (ProbComp.eval (P.serverQuery s i) q).toReal then
            (ProbComp.eval (P.serverQuery s i) q).toReal -
              (ProbComp.eval (P.serverQuery s i₀) q).toReal
          else 0 := by
      rw [PMF.toReal_false_eq_one_sub, mul_sub, mul_one, mul_keepProb_eq_min]
      by_cases hlt :
          (ProbComp.eval (P.serverQuery s i₀) q).toReal <
            (ProbComp.eval (P.serverQuery s i) q).toReal
      · rw [ite_eq_left hlt, min_eq_left hlt.le]
      · rw [ite_eq_right hlt, min_eq_right (le_of_not_gt hlt), sub_self]
    simp only [hterm_eq]
    let E : Set Q := {q |
      (ProbComp.eval (P.serverQuery s i₀) q).toReal <
        (ProbComp.eval (P.serverQuery s i) q).toReal}
    have hdiff :
        (∑ q : Q,
          if (ProbComp.eval (P.serverQuery s i₀) q).toReal <
              (ProbComp.eval (P.serverQuery s i) q).toReal then
            (ProbComp.eval (P.serverQuery s i) q).toReal -
              (ProbComp.eval (P.serverQuery s i₀) q).toReal
          else 0) =
          ((ProbComp.eval (P.serverQuery s i)).toOuterMeasure E).toReal -
            ((ProbComp.eval (P.serverQuery s i₀)).toOuterMeasure E).toReal := by
      rw [PMF.toOuterMeasure_apply_toReal, PMF.toOuterMeasure_apply_toReal,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      change (if q ∈ E then _ else 0) =
        (if q ∈ E then _ else 0) - (if q ∈ E then _ else 0)
      split_ifs <;> ring
    rw [hdiff]
    have habs := (hpriv s i).abs_toReal_sub_le hδ E
    exact (le_abs_self _).trans habs
  -- Convert `hpir_ennreal` to `ℝ`:
  have hsum_ne_top :
      (∑ k : Fin (Fintype.card S),
        ((ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
          fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) none) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => PMF.apply_ne_top _ _
  have hrhs_ne_top :
      decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) (x i) +
        (2 : ℝ≥0∞)⁻¹ * ∑ k : Fin (Fintype.card S),
          ((ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
            fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) none ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.mul_ne_top (by simp) hsum_ne_top⟩
  have hreal := ENNReal.toReal_mono hrhs_ne_top hpir_ennreal
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (ENNReal.mul_ne_top (by simp) hsum_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _] at hreal
  have hsum_le :
      (∑ k : Fin (Fintype.card S),
        (((ProbComp.eval (P.serverQuery (eS.symm k) i)).bind
          fun q => ProbComp.eval (smoothSlotCoins P i₀ i (eS.symm k) q)) none).toReal) ≤
        Fintype.card S * δ := by
    calc _ ≤ ∑ _k : Fin (Fintype.card S), δ := Finset.sum_le_sum fun k _ => hfail_le k
      _ = Fintype.card S * δ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hpir := hrec x i
  linarith

/-- **GKST Lemma 7.1 (general `k = |S|` servers)**: a one-round PIR scheme `P` whose server query
distributions are `δ`-close (`CloseTo`) to those at the reference index `i₀` (in particular when
pairwise `δ`-close) and which recovers each bit with probability at least `1 / 2 + ε` yields a
`(|S|, |S| + 1, ε - |S| · δ / 2)`-smooth decoder for `smoothCode P i₀` (with codeword length
`≤ (|S| + 1) · |S| · |Q|`)
[GKST, Section 7.1, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]. -/
theorem isSmoothDecoder_smoothDecoder (P : Scheme ι S R Q A) [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (i₀ : ι) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hpriv : ∀ s i,
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i₀))
        (ENNReal.ofReal δ))
    (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal) :
    IsSmoothDecoder (smoothCode P i₀) (Fintype.card S) (Fintype.card S + 1)
      (ε - Fintype.card S * δ / 2) (smoothDecoder P i₀) where
  isQueryBounded := isQueryBounded_smoothDecoder P i₀
  correct := toReal_decodeLaw_smoothDecoder_ge P i₀ hδ hpriv hrec
  smooth x i j := expectedReads_smoothDecoder_le P i₀ (smoothCode P i₀ x) i j

/-- **GKST Lemma 7.1 (two servers)**: a `(1 - δ)`-statistically-private two-server PIR scheme with
recovery probability at least `1 / 2 + ε` yields a `(2, 3, ε - δ)`-smooth code of length at most
`6 · |Q|` [GKST, Section 7.1, Lemma 7.1][GoldreichKarloffSchulmanTrevisan2006]. -/
theorem isSmoothDecoder_smoothDecoder_two (P : Scheme ι S R Q A) [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (hS : Fintype.card S = 2) (i₀ : ι) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hpriv : ∀ s i,
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i₀))
        (ENNReal.ofReal δ))
    (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal) :
    IsSmoothDecoder (smoothCode P i₀) 2 3 (ε - δ) (smoothDecoder P i₀) := by
  have h := isSmoothDecoder_smoothDecoder P i₀ hδ hpriv hrec
  rw [hS] at h
  have hc : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  have hε : ε - ((2 : ℕ) : ℝ) * δ / 2 = ε - δ := by push_cast; ring
  rwa [hc, hε] at h

/-! ### Perfect-privacy specializations (`δ = 0`) -/

/-- Under perfect privacy (`P.IsPrivate`), `smoothDecoder P i₀` never enters failure mode, so its
output law on `smoothCode P i₀ x` equals `ProbComp.eval (P.run x i)` exactly. -/
theorem decodeLaw_smoothDecoder_of_isPrivate (P : Scheme ι S R Q A) [Fintype S]
    [Fintype Q] [DecidableEq Q] (hpriv : P.IsPrivate) (i₀ : ι) (x : ι → Bool) (i : ι) :
    decodeLaw (smoothDecoder P i₀ i) (smoothCode P i₀ x) = ProbComp.eval (P.run x i) := by
  let eS := Fintype.equivFin S
  have hkeep (s : S) (q : Q) : smoothKeepRatio P i₀ i s q = 1 := by
    simp [smoothKeepRatio_eq, ProbComp.evalRat_eq_of_eval_eq (hpriv.eval_serverQuery_eq s i i₀)]
  have hslot (s : S) (q : Q) :
      ProbComp.eval (smoothSlotCoins P i₀ i s q) =
        (let _ : Nonempty (Fin (smoothCopies P i₀ (s, q))) :=
          ⟨⟨0, smoothCopies_pos P i₀ (s, q)⟩⟩
         (PMF.uniformOfFintype (Fin (smoothCopies P i₀ (s, q)))).map
          fun idx => some (⟨(s, q), idx⟩ : SmoothPos P i₀)) := by
    let _ : Nonempty (Fin (smoothCopies P i₀ (s, q))) := ⟨⟨0, smoothCopies_pos P i₀ (s, q)⟩⟩
    rw [smoothSlotCoins, hkeep, ProbComp.eval_bind, ProbComp.eval_bernoulliRat_of_one_le le_rfl,
      PMF.pure_bind]
    simp [ProbComp.eval_uniform, PMF.map]
  simp only [smoothDecoder, smoothCoins, decodeLaw_bind, decodeLaw_sample, P.eval_run,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind,
    decodeLaw_smoothDecoder_branch]
  rw [PMF.map]
  refine congrArg (ProbComp.eval (P.query i)).bind (funext fun rq => ?_)
  have hconst : ∀ g : Bool,
      ((ProbComp.eval (OracleComp.pi fun k : Fin (Fintype.card S) =>
        smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k)))).bind fun slots =>
          if h : ∀ idx, (slots idx).isSome then
            PMF.pure (P.reconstruct i rq.1
              fun s => smoothCode P i₀ x ((slots (eS s)).get (h (eS s))))
          else
            PMF.pure g) =
        PMF.pure (P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)) := by
    intro g
    have hcongr := ProbComp.eval_pi_congr (m := Fintype.card S)
      (p := fun k => smoothSlotCoins P i₀ i (eS.symm k) (rq.2 (eS.symm k)))
      (q := fun k =>
        let _ : Nonempty (Fin (smoothCopies P i₀ (eS.symm k, rq.2 (eS.symm k)))) :=
          ⟨⟨0, smoothCopies_pos P i₀ _⟩⟩
        (fun idx => some (⟨(eS.symm k, rq.2 (eS.symm k)), idx⟩ : SmoothPos P i₀)) <$>
          ProbComp.uniform (Fin (smoothCopies P i₀ (eS.symm k, rq.2 (eS.symm k)))))
      (fun k => by
        let _ : Nonempty (Fin (smoothCopies P i₀ (eS.symm k, rq.2 (eS.symm k)))) :=
          ⟨⟨0, smoothCopies_pos P i₀ _⟩⟩
        rw [hslot, ProbComp.eval_map, ProbComp.eval_uniform])
    rw [hcongr, ProbComp.eval_pi_map, PMF.bind_map]
    have hbody : ∀ u : (k : Fin (Fintype.card S)) →
        Fin (smoothCopies P i₀ (eS.symm k, rq.2 (eS.symm k))),
        (if h : ∀ idx : Fin (Fintype.card S),
            (some (⟨(eS.symm idx, rq.2 (eS.symm idx)), u idx⟩ : SmoothPos P i₀)).isSome then
          PMF.pure (P.reconstruct i rq.1 fun s =>
            smoothCode P i₀ x
              ((some (⟨(eS.symm (eS s), rq.2 (eS.symm (eS s))), u (eS s)⟩ : SmoothPos P i₀)).get
                (h (eS s))))
        else
          PMF.pure g) =
          PMF.pure (P.reconstruct i rq.1 fun s => P.answer s x (rq.2 s)) := by
      intro u
      have hisSome : ∀ idx : Fin (Fintype.card S),
          (some (⟨(eS.symm idx, rq.2 (eS.symm idx)), u idx⟩ : SmoothPos P i₀)).isSome :=
        fun _ => rfl
      rw [dite_eq_left hisSome]
      congr 1
      congr 1
      funext s
      simp [smoothCode]
    refine (congrArg (ProbComp.eval _).bind (funext fun u => hbody u)).trans ?_
    exact PMF.bind_const _ _
  rw [congrArg (PMF.uniformOfFintype Bool).bind (funext hconst), PMF.bind_const]
  rfl

/-- **Perfect-privacy PIR-to-smooth-code converse** (`δ = 0` specialization of GKST Lemma 7.1;
at `|S| = 2`, [Kerenidis and de Wolf, Appendix B, Lemma 3][KerenidisDeWolf2004]): a perfectly
private `k`-server PIR scheme with recovery probability at least `1 / 2 + ε` yields a
`(|S|, |S| + 1, ε)`-smooth decoder for `smoothCode P i₀` (with codeword length
`≤ (|S| + 1) · |S| · |Q|`). -/
theorem isSmoothDecoder_smoothDecoder_of_isPrivate (P : Scheme ι S R Q A)
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] (hpriv : P.IsPrivate) (i₀ : ι)
    {ε : ℝ} (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal) :
    IsSmoothDecoder (smoothCode P i₀) (Fintype.card S) (Fintype.card S + 1) ε
      (smoothDecoder P i₀) := by
  have hclose : ∀ s i,
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i₀))
        (ENNReal.ofReal 0) := by
    intro s i
    rw [ENNReal.ofReal_zero, hpriv.eval_serverQuery_eq s i i₀]
    exact CloseTo.refl _
  simpa using isSmoothDecoder_smoothDecoder P i₀ le_rfl hclose hrec

/-- Perfectly correct and perfectly private `k`-server PIR yields a `(|S|, |S| + 1, 1 / 2)`-smooth
code of length at most `(|S| + 1) · |S| · |Q|`
(converse to `PIR.SmoothCode.hasScheme_ofDecoder`). -/
theorem isSmoothDecoder_smoothDecoder_of_isCorrect (P : Scheme ι S R Q A)
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] (hcorrect : P.IsCorrect)
    (hpriv : P.IsPrivate) (i₀ : ι) :
    IsSmoothDecoder (smoothCode P i₀) (Fintype.card S) (Fintype.card S + 1) (1 / 2)
      (smoothDecoder P i₀) := by
  refine isSmoothDecoder_smoothDecoder_of_isPrivate P hpriv i₀ fun x i => ?_
  rw [P.isCorrect_iff_eval_run.mp hcorrect x i, PMF.pure_apply, ite_eq_left rfl,
    ENNReal.toReal_one]
  linarith

/-! ### Predetermined answer coordinates (GKST Lemma 7.1, item 2) -/

/-- **Predetermined answer-coordinate preservation**
([GKST, Lemma 7.1, item 2][GoldreichKarloffSchulmanTrevisan2006]): when `P.reconstruct i r` inspects
at most a predetermined coordinate subset `sel i r s : Finset κ` of each server's answer
`a s : κ → γ` (for example, `k` predetermined bit positions out of an `a`-bit answer), masking
every coordinate outside `sel i st.state s` in the retrieved codeword symbols with any `pad : γ`
leaves `smoothDecoder P i₀ i` unchanged. Together with `smoothCoins P i₀ i`, this exhibits both the
queried codeword positions `st.slots` and the predetermined coordinate subsets `sel i st.state s`
for each coin draw `st`. -/
theorem smoothDecoder_eq_of_predetermined {κ γ : Type} [DecidableEq κ]
    (P : Scheme ι S R Q (κ → γ)) [Fintype S] [Fintype Q] [DecidableEq Q] (i₀ : ι)
    (sel : ι → R → S → Finset κ) (pad : γ)
    (hpred : ∀ i r (a a' : S → κ → γ),
      (∀ s, ∀ b ∈ sel i r s, a s b = a' s b) → P.reconstruct i r a = P.reconstruct i r a')
    (i : ι) :
    smoothDecoder P i₀ i = (do
      let st ← sample (smoothCoins P i₀ i)
      if h : ∀ idx, (st.slots idx).isSome then
        let ans ← readAll fun idx => (st.slots idx).get (h idx)
        let masked : S → κ → γ := fun s b =>
          if b ∈ sel i st.state s then ans (Fintype.equivFin S s) b else pad
        pure (P.reconstruct i st.state masked)
      else
        pure st.guess) := by
  simp only [smoothDecoder]
  congr 1 with st
  split_ifs with h
  · congr 1 with ans
    refine congrArg pure (hpred i st.state _ _ fun s b hb => ?_)
    simp [hb]
  · rfl

/-! ### Single-server noisy and statistically-private answer-size lower bounds -/

/-- **Noisy / statistically-private single-server PIR answer-size lower bound** (combining GKST
Lemma 7.1 at `|S| = 1` with `Code.IsSmoothDecoder.four_mul_card_mul_sq_le` from `OneQuery.lean`):
any one-server PIR scheme over a finite query set whose query distributions are pairwise `δ`-close
(`0 ≤ δ`) and which recovers each database bit with probability at least `1 / 2 + ε` (`δ / 2 ≤ ε`)
has answer alphabet size satisfying `|ι| · (ε - δ / 2)² ≤ |A| - 1`. -/
theorem card_mul_sq_le_card_answer_sub_one_of_statPrivate (P : Scheme ι S R Q A)
    [Fintype ι] [Unique S] [Finite Q] [Fintype A] [Nonempty A] {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : δ / 2 ≤ ε)
    (hpriv : ∀ s i i',
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i'))
        (ENNReal.ofReal δ))
    (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal) :
    (Fintype.card ι : ℝ) * (ε - δ / 2) ^ 2 ≤ Fintype.card A - 1 := by
  classical
  let _ : Fintype S := Unique.fintype
  cases nonempty_fintype Q
  rcases isEmpty_or_nonempty ι with hι | hne
  · rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
    have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
    linarith
  · obtain ⟨i₀⟩ := hne
    have hcardS : Fintype.card S = 1 := Fintype.card_unique
    have hsm := isSmoothDecoder_smoothDecoder P i₀ hδ (fun s i => hpriv s i i₀) hrec
    rw [hcardS] at hsm
    have h1 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    have hε' : ε - ((1 : ℕ) : ℝ) * δ / 2 = ε - δ / 2 := by push_cast; ring
    rw [h1, hε'] at hsm
    have hfour := hsm.four_mul_card_mul_sq_le (by linarith)
    linarith

/-- **Noisy perfectly-private single-server PIR answer-size lower bound** (`δ = 0` case of
`card_mul_sq_le_card_answer_sub_one_of_statPrivate`): any perfectly private one-server PIR scheme
over a finite query set recovering each bit with probability at least `1 / 2 + ε` (`0 ≤ ε`)
satisfies `|ι| · ε² ≤ |A| - 1`. -/
theorem card_mul_sq_le_card_answer_sub_one_of_isPrivate (P : Scheme ι S R Q A)
    [Fintype ι] [Unique S] [Finite Q] [Fintype A] [Nonempty A] (hpriv : P.IsPrivate) {ε : ℝ}
    (hε : 0 ≤ ε) (hrec : ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal) :
    (Fintype.card ι : ℝ) * ε ^ 2 ≤ Fintype.card A - 1 := by
  have hclose : ∀ s i i',
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i'))
        (ENNReal.ofReal 0) := by
    intro s i i'
    rw [ENNReal.ofReal_zero, hpriv.eval_serverQuery_eq s i i']
    exact CloseTo.refl _
  simpa using card_mul_sq_le_card_answer_sub_one_of_statPrivate P le_rfl (by linarith) hclose hrec

end SmoothDecoder

end Cslib.Crypto.Protocols.PIR
