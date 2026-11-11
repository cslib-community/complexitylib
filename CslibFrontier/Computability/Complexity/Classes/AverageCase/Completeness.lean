/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.BoundedHalting
public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Compression
public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.Nat.Doubling
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PolyTime

/-!
# Levin's theorem: bounded halting is complete for `DistNP`

[Bogdanov and Trevisan, Theorem 19][BogdanovTrevisan2006], after [Levin][Levin1986]: the
distributional bounded halting problem `(BH, U^BH)` is complete for `DistNP = (NP, PComp)` under
distributional reductions (`Cslib.Complexity.DistReduction`).

Let `(L, D) ∈ DistNP`, with an `NP` verifier `V` for `L` and a cumulative distribution `num / den`
of `D`. The reduction maps `x` of length `n` to the instance `(c, C(x), 1^{t(x)})`, where

* `C(x) = frame (lenWord n) ++ compress x` (`Cslib.Complexity.BoundedHalting.code`) is the code of
  Claim 20 (`Cslib.Complexity.Compression.compress`) prefixed with the length of `x`. The prefix
  makes `C` injective on all words, so a program can recover `x` from `C(x)` without knowing `n`.
* `c` is the program of a polynomial-time machine for the verifier
  `Cslib.Complexity.BoundedHalting.codeVerifier`, which on `(z, v)` decodes `x` and a certificate
  `w` from `v`, checks `z = C(x)` and `|w| = q(|x|)`, and runs `V (x, w)`.
* `t(x) = N(n) - |header c (C x)|`, where the polynomial `N` makes every instance have length
  exactly `N(n)` and leaves a clock of at least the running time of the machine on
  `(C(x), frame x ++ w)`.

Correctness holds for every `x`. For domination, the reduction is injective and
`U^BH_{N(n)}(f x) = 2^{-|header c (C x)|}`, and Claim 20 bounds `2^{|C x|} D_n(x) ≤ 2`, so
`D_n(x) ≤ P(n) U^BH_{N(n)}(f x)` with `P(n) = 2^{2|c|+4} (6n+5)^2 (2n+1)^2`
(`Cslib.Complexity.BoundedHalting.two_pow_length_header_code_mul_le`).

## Main results

* `Cslib.Complexity.BoundedHalting.distHard_problem`: every problem of `DistNP` reduces to
  `(BH, U^BH)`.
* `Cslib.Complexity.BoundedHalting.distComplete_problem`: `(BH, U^BH)` is complete for `DistNP`.
* `Cslib.Complexity.BoundedHalting.problem_mem_AvgP_iff`,
  `Cslib.Complexity.BoundedHalting.problem_mem_HeurP_iff`: `(BH, U^BH)` is in `AvgP` (resp.
  `HeurP`) exactly when all of `DistNP` is.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
* [L. A. Levin, *Average Case Complete Problems*][Levin1986]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM Kolmogorov.DescriptionMethod

namespace BoundedHalting

variable {num den : List Bool → ℕ}

/-- The code of `x`: its length in binary, framed, followed by the compression of `x`. -/
def code (num den : List Bool → ℕ) (x : List Bool) : List Bool :=
  frame (lenWord x.length) ++ Compression.compress num den x

/-- The verifier simulated by the program of the reduction: on `(z, v)`, decode `x` and a
certificate `w` from `v`, check that `z` is the code of `x` and `w` has the right length, and run
the verifier `V` of the source problem. -/
def codeVerifier (num den : List Bool → ℕ) (q : Polynomial ℕ)
    (V : List Bool × List Bool → Bool) (zv : List Bool × List Bool) : Bool :=
  decide (zv.1 = code num den (unframe zv.2)) &&
    decide ((dropFrame zv.2).length = q.eval (unframe zv.2).length) &&
    V (unframe zv.2, dropFrame zv.2)

/-- The code is computable in polynomial time. -/
theorem code_polyTime (hnum : ComputableInPolyTime num encBits encNat)
    (hden : ComputableInPolyTime den encBits encNat) :
    ComputableInPolyTime (code num den) encBits encBits := by
  have hl := lenWord_polyTime.comp ComputableInPolyTime.length_bits
  have hc := Compression.compress_polyTime hnum hden
  unfold code
  polytime

/-- The verifier simulated by the reduction is computable in polynomial time. -/
theorem codeVerifier_polyTime (hnum : ComputableInPolyTime num encBits encNat)
    (hden : ComputableInPolyTime den encBits encNat) (q : Polynomial ℕ)
    {V : List Bool × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) :
    ComputableInPolyTime (codeVerifier num den q V) (encPair encBits encBits) encBool := by
  have hcode := code_polyTime hnum hden
  have h1 := ComputableInPolyTime.fst encBits encBits
  have h2 := ComputableInPolyTime.snd encBits encBits
  have hx := ComputableInPolyTime.unframe.comp h2
  have hw := ComputableInPolyTime.dropFrame.comp h2
  have hq := (ComputableInPolyTime.unary_eval q).comp (ComputableInPolyTime.length_bits.comp hx)
  have hV' := hV.comp (hx.prod hw)
  have hd1 := ComputableInPolyTime.decide_eq' h1 (hcode.comp hx)
  have hd2 := ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits.comp hw) hq
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hd1 hd2) hV'

section Spec

variable {D : Ensemble} (hcdf : ∀ x, D.cdf x = (num x : ℝ≥0∞) / den x) (hden : ∀ x, den x ≠ 0)
include hcdf hden

/-- `|C(x)| ≤ 3|x| + 2`. -/
theorem length_code_le (x : List Bool) : (code num den x).length ≤ 3 * x.length + 2 := by
  have h1 := Compression.length_compress_le hcdf hden x
  have h2 := Nat.size_le_self x.length
  simp only [code, List.length_append, length_frame, length_lenWord]
  omega

/-- The header of a reduced instance has length at most `2|c| + 9|x| + 8`. -/
theorem length_header_code_le (c x : List Bool) :
    (header c (code num den x)).length ≤ 2 * c.length + 9 * x.length + 8 := by
  have h1 := length_code_le hcdf hden x
  have h2 := Nat.size_le_self (code num den x).length
  rw [length_header]
  omega

/-- The code is injective. -/
theorem code_injective {x x' : List Bool} (h : code num den x = code num den x') : x = x' := by
  obtain ⟨h1, h2⟩ := frame_append_inj h
  have hlen : x.length = x'.length := by
    simpa using congrArg BitString.binaryValue h1
  exact Compression.compress_injective hcdf hden hlen h2

/-- **Domination by the header weight**:
`2^{|header c (C x)|} D_n(x) ≤ 2^{2|c|+4} (6n+5)^2 (2n+1)^2`, the inequality
`D_n(x) ≤ poly(n) U^BH(f x)` of the source. -/
theorem two_pow_length_header_code_mul_le (c x : List Bool) :
    (2 : ℝ≥0∞) ^ (header c (code num den x)).length * D.dist x.length x ≤
      ((2 ^ (2 * c.length + 4) * (6 * x.length + 5) ^ 2 * (2 * x.length + 1) ^ 2 : ℕ) :
        ℝ≥0∞) := by
  have hC := Compression.two_pow_length_compress_mul_le hcdf hden x
  have hz := length_code_le hcdf hden x
  have hA : 2 ^ (2 * c.length + 1 + (2 * (code num den x).length.size + 1) +
      2 * x.length.size + 1) * 2 ≤
      2 ^ (2 * c.length + 4) * (6 * x.length + 5) ^ 2 * (2 * x.length + 1) ^ 2 := by
    have h1 : 2 ^ (2 * (code num den x).length.size) ≤ (6 * x.length + 5) ^ 2 := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left ((Nat.two_pow_size_le _).trans (by omega)) 2
    have h2 : 2 ^ (2 * x.length.size) ≤ (2 * x.length + 1) ^ 2 := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left (Nat.two_pow_size_le _) 2
    calc 2 ^ (2 * c.length + 1 + (2 * (code num den x).length.size + 1) +
          2 * x.length.size + 1) * 2 =
        2 ^ (2 * c.length + 4) * 2 ^ (2 * (code num den x).length.size) *
          2 ^ (2 * x.length.size) := by
          rw [← pow_succ, ← pow_add, ← pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have hlen : (header c (code num den x)).length =
      (2 * c.length + 1 + (2 * (code num den x).length.size + 1) + 2 * x.length.size + 1) +
        (Compression.compress num den x).length := by
    rw [length_header]
    simp only [code, List.length_append, length_frame, length_lenWord]
    omega
  rw [hlen, pow_add, mul_assoc]
  calc (2 : ℝ≥0∞) ^ (2 * c.length + 1 + (2 * (code num den x).length.size + 1) +
        2 * x.length.size + 1) * (2 ^ (Compression.compress num den x).length * D.dist x.length x)
      ≤ (2 : ℝ≥0∞) ^ (2 * c.length + 1 + (2 * (code num den x).length.size + 1) +
        2 * x.length.size + 1) * 2 := mul_le_mul_of_nonneg_left hC zero_le
    _ ≤ _ := by exact_mod_cast hA

end Spec

/-- A machine that computes `out` from `w` within `T` steps returns it under every clock
`t ≥ T`. -/
private theorem runFor_eq_of_computesInTimeAndSpace {k : ℕ} {State : Type}
    {tm : Turing.MultiTapeTM k Bool State} {w out : List Bool} {T s t : ℕ}
    (h : tm.ComputesInTimeAndSpace w out T s) (ht : T ≤ t) :
    tm.runFor w t = some out := by
  obtain ⟨hh, ho⟩ := h.runFrom_of_le ht
  exact (tm.mem_runFor_iff).mpr ⟨hh, ho⟩

/-- A clocked run that returns `out'` agrees with the output of the machine. -/
private theorem eq_of_runFor_eq {k : ℕ} {State : Type} {tm : Turing.MultiTapeTM k Bool State}
    {w out out' : List Bool} {T s t : ℕ} (h : tm.ComputesInTimeAndSpace w out T s)
    (h' : tm.runFor w t = some out') : out' = out := by
  have h1 := (tm.mem_runFor_iff).mp h'
  rcases le_total T t with hTt | htT
  · obtain ⟨-, ho⟩ := h.runFrom_of_le hTt
    rw [← h1.2, ho]
  · obtain ⟨-, ho⟩ := h.runFrom_of_le (le_refl T)
    rw [← h1.2, ← ho, tm.runFrom_eq_of_halt _ htT h1.1]

/-- **Levin's theorem** [Bogdanov and Trevisan, Theorem 19][BogdanovTrevisan2006]: every problem of
`DistNP` reduces to the distributional bounded halting problem `(BH, U^BH)`. -/
theorem distHard_problem : DistHard DistNP problem := by
  intro L hL
  obtain ⟨⟨q, V, hVpoly, hVer⟩, num, den, hnum, hden, hden0, hcdf⟩ := mem_DistNP.mp hL
  obtain ⟨T, s, hT, -, k, State, hfin, tm, htm⟩ := codeVerifier_polyTime hnum hden q hVpoly
  obtain ⟨c, hc⟩ : ∃ c : List Bool, ∀ w t,
      universalTMRunFor (frame c ++ w) t = tm.runFor w t := by
    have := Fintype.ofFinite State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    exact ⟨Universal.eDesc (Universal.desc eS Universal.eBit tm),
      universalTMRunFor_frame_eDesc_append eS tm⟩
  obtain ⟨cT, dT, hTle⟩ := polynomiallyBounded_iff_le.mp hT
  -- the clock: enough for the verifier on `(code x, frame x ++ w)`
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℕ, ∀ n, R.eval n =
      cT * (8 * n + 7 + q.eval n) ^ dT + (2 * n + 1 + q.eval n) :=
    ⟨Polynomial.C cT * (Polynomial.C 8 * Polynomial.X + Polynomial.C 7 + q) ^ dT +
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 1 + q), fun n => by simp⟩
  -- the length of the instances
  obtain ⟨N, hN⟩ : ∃ N : Polynomial ℕ, ∀ n, N.eval n = R.eval n + (2 * c.length + 9 * n + 8) :=
    ⟨R + Polynomial.C (2 * c.length + 8) + Polynomial.C 9 * Polynomial.X, fun n => by
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      ring⟩
  -- the domination factor
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℕ, ∀ n, P.eval n =
      2 ^ (2 * c.length + 4) * (6 * n + 5) ^ 2 * (2 * n + 1) ^ 2 :=
    ⟨Polynomial.C (2 ^ (2 * c.length + 4)) * (Polynomial.C 6 * Polynomial.X + Polynomial.C 5) ^ 2 *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) ^ 2, fun n => by simp⟩
  obtain ⟨f, hf⟩ : ∃ f : List Bool → List Bool, ∀ x, f x =
      encode c (code num den x) (N.eval x.length - (header c (code num den x)).length) :=
    ⟨_, fun _ => rfl⟩
  have hhead (x : List Bool) : (header c (code num den x)).length ≤ N.eval x.length := by
    have := length_header_code_le hcdf hden0 c x
    rw [hN]
    omega
  have hflen (x : List Bool) : (f x).length = N.eval x.length := by
    rw [hf, length_encode]
    have := hhead x
    omega
  have hfinj : Function.Injective f := fun x x' h => by
    rw [hf, hf] at h
    exact code_injective hcdf hden0 (encode_injective h).2.1
  have hfpoly : ComputableInPolyTime f encBits encBits := by
    have hcode := code_polyTime hnum hden
    have hh : ComputableInPolyTime (fun x => (header c (code num den x)).length) encBits
        encUnary :=
      ComputableInPolyTime.length_bits.comp
        (header_polyTime.comp ((ComputableInPolyTime.const c).prod hcode))
    have hNx : ComputableInPolyTime (fun x : List Bool => N.eval x.length) encBits encUnary :=
      (ComputableInPolyTime.unary_eval N).comp ComputableInPolyTime.length_bits
    have := encode_polyTime (ComputableInPolyTime.const c) hcode
      (ComputableInPolyTime.unary_sub' hNx hh)
    rw [show f = _ from funext hf]
    exact this
  refine ⟨⟨f, fun n => N.eval n, P, hfpoly, fun n x _ => ?_, fun n y => ?_⟩⟩
  · -- correctness
    rw [problem_lang, hf, encode_mem_BH_iff, accepts_iff]
    have hhx := hhead x
    have hRle : R.eval x.length ≤ N.eval x.length - (header c (code num den x)).length := by
      have := length_header_code_le hcdf hden0 c x
      rw [hN] at hhx ⊢
      omega
    constructor
    · intro hx
      obtain ⟨w, hw, hVw⟩ := (hVer x).mp hx
      simp only [encBits_apply] at hw
      have hlen : (encPair encBits encBits (code num den x, frame x ++ w)).length ≤
          8 * x.length + 6 + q.eval x.length := by
        have := length_code_le hcdf hden0 x
        simp only [encPair_apply, encBits_apply, List.length_append, length_frame]
        omega
      have hTb : T (encPair encBits encBits (code num den x, frame x ++ w)).length ≤
          R.eval x.length := by
        rw [hR]
        calc T _
            ≤ cT * ((encPair encBits encBits (code num den x, frame x ++ w)).length + 1) ^ dT :=
              hTle _
          _ ≤ cT * (8 * x.length + 7 + q.eval x.length) ^ dT :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
          _ ≤ _ := Nat.le_add_right _ _
      have hwR : 2 * x.length + 1 + q.eval x.length ≤ R.eval x.length := by
        rw [hR]
        exact Nat.le_add_left _ _
      refine ⟨frame x ++ w, ?_, ?_⟩
      · simp only [List.length_append, length_frame]
        omega
      · rw [hc, show frame (code num den x) ++ (frame x ++ w) =
            encPair encBits encBits (code num den x, frame x ++ w) by
          rw [encPair_apply]; rfl]
        rw [runFor_eq_of_computesInTimeAndSpace (htm (code num den x, frame x ++ w))
          (hTb.trans hRle)]
        have hv : codeVerifier num den q V (code num den x, frame x ++ w) = true := by
          simp only [codeVerifier, unframe_frame_append, dropFrame_frame_append, hw, hVw,
            decide_true, Bool.and_self]
        rw [hv]
        rfl
    · rintro ⟨v, -, hrun⟩
      rw [hc, show frame (code num den x) ++ v = encPair encBits encBits (code num den x, v) by
        rw [encPair_apply]; rfl] at hrun
      have hout := eq_of_runFor_eq (htm (code num den x, v)) hrun
      have hv : codeVerifier num den q V (code num den x, v) = true := by
        simpa only [encBool_apply, List.cons.injEq, and_true] using hout.symm
      simp only [codeVerifier, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hcx, hq⟩, hV⟩ := hv
      rw [code_injective hcdf hden0 hcx]
      exact (hVer _).mpr ⟨dropFrame v, by simpa only [encBits_apply] using hq, hV⟩
  · -- domination
    by_cases hy : ∃ x ∈ (L.ens.dist n).support, f x = y
    · obtain ⟨x, hx, rfl⟩ := hy
      obtain rfl := L.ens.length_eq n x hx
      rw [Probability.PMF.map_apply_of_injective _ hfinj, problem_ens, ← hflen x, hf,
        uniformBH_dist_encode, hP]
      have hkey := two_pow_length_header_code_mul_le hcdf hden0 c x
      have h0 : (2 : ℝ≥0∞) ^ (header c (code num den x)).length ≠ 0 := pow_ne_zero _ two_ne_zero
      have htop : (2 : ℝ≥0∞) ^ (header c (code num den x)).length ≠ ⊤ :=
        ENNReal.pow_ne_top ENNReal.ofNat_ne_top
      calc L.ens.dist x.length x
          = (2 ^ (header c (code num den x)).length)⁻¹ *
              (2 ^ (header c (code num den x)).length * L.ens.dist x.length x) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
        _ ≤ (2 ^ (header c (code num den x)).length)⁻¹ *
              ((2 ^ (2 * c.length + 4) * (6 * x.length + 5) ^ 2 * (2 * x.length + 1) ^ 2 : ℕ) :
                ℝ≥0∞) := mul_le_mul_of_nonneg_left hkey zero_le
        _ = _ := mul_comm _ _
    · have hzero : (L.ens.dist n).map f y = 0 := by
        rw [PMF.apply_eq_zero_iff, PMF.support_map]
        rintro ⟨x, hx, rfl⟩
        exact hy ⟨x, hx, rfl⟩
      rw [hzero]
      exact zero_le

/-- **Levin's theorem** [Bogdanov and Trevisan, Theorem 19][BogdanovTrevisan2006]: the
distributional bounded halting problem `(BH, U^BH)` is complete for `DistNP`. -/
theorem distComplete_problem : DistComplete DistNP problem :=
  ⟨problem_mem_DistNP, distHard_problem⟩

/-- `(BH, U^BH)` has an errorless heuristic scheme exactly when every problem of `DistNP` does. -/
theorem problem_mem_AvgP_iff : problem ∈ AvgP ↔ DistNP ⊆ AvgP :=
  distComplete_problem.mem_AvgP_iff

/-- `(BH, U^BH)` has a heuristic scheme exactly when every problem of `DistNP` does. -/
theorem problem_mem_HeurP_iff : problem ∈ HeurP ↔ DistNP ⊆ HeurP :=
  distComplete_problem.mem_HeurP_iff

end BoundedHalting

end Cslib.Complexity
