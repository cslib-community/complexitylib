/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.HeavyBranchFold
public import Complexity.Computability.PolyTime.FineGrained.ParameterCheck
import Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.Nat.CeilDiv
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.SqrtLog
import Mathlib.Tactic.Linarith

/-!
# High-incidence branching for Lemma D.2

Lemma D.2 of [OpenAI2026ETH] (p. 54) counts the common zeros of a sparse polynomial system over
`𝔽₂` by tensor contraction. The first step of its proof (p. 54) fixes, in all possible ways, the
variables that belong to more than

`D* = max{1, ⌈N₀ / n⌉} ⌈√λ⌉`

scopes, where `λ = ⌈log₂ n⌉` and `N₀ = ∑_i |I_i|` is the number of pairs `(i, v)` with `v` in the
scope `I_i` of test `i`. This file defines that threshold and proves what the proof uses about it.
The branching itself is `HeavyBranchFold.countByBranching`, with its exactness and its streaming
time and space bounds.

* **Threshold** (`threshold`). `D*` reuses the §5.5 selector
  `ParameterCheck.heavyIncidenceCutoff` at `max 1 N₀`, and `threshold_eq_ceil` states the source's
  formula. It is polynomial-time (`computableInPolyTime_threshold`).
* **Few branching variables.** At most `n / ⌈√λ⌉` variables exceed `D*`
  (`length_branchVars_le`), so there are at most `2 ^ (n / ⌈√λ⌉)` branches. Every reduced branch
  keeps `n' ≥ n / 2` free variables (`IsReducedBranch.le_two_mul`) and is no longer to encode than
  its parent (`IsReducedBranch.length_enc_le`).
* **Polylogarithmic threshold.** Under the hypotheses of Lemma D.2 (`IsSparseSystem k c n`),
  `D* ≤ max{1, c k λ^c} ⌈√λ⌉` (`threshold_le`), hence `D* ≤ λ ^ (c + 2)` once `c k ≤ λ`
  (`threshold_le_pow`).
* **The branching instance.** For `n ≥ 5` and `2 ^ ((c + 1) k) ≤ n`, every reduced branch
  `(n', sys')` satisfies the branch hypotheses `IsSparseBranch k (2 c + 4) n' sys'`, stated at the
  branch's own variable count (`isSparseBranch_of_isReducedBranch`). These are the hypotheses that
  the branch solver consumes: they bound the number of equations by `(2c + 4) n'`, and the
  monomials, scope and incidences by `⌈log₂ n'⌉ ^ (2c + 4)`.
* **The counter** (`count`). It is exact whenever the branch solver is exact on reduced branches
  (`count_eq_rootCount`, `count_eq_commonZeroCount`). For a solver certificate, it has a
  certificate whose time is `(2 ^ |S| + 1) (K (|x| + 1) ^ K + R)` and whose space is
  `K (|x| + 1) ^ K + Q`, where `R` and `Q` bound the solver on the reduced branches and `K` does not
  depend on the solver (`exists_count_certificate`).

The source normalizes the system before branching. Here the system is assumed normalized
(`IsCanonicalEquation`), as `HeavyBranchFold.substituteEquation` keeps it on every branch.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.threshold`: the threshold `D*`.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.branchVars`: the variables above `D*`.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsReducedBranch`: the reduced branches.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.count`: the counter, branching on
  `branchVars` and calling a solver on each reduced branch.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsSparseSystem`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsSparseBranch`: the hypotheses of
  Lemma D.2, and those of its branch solver.

## Main results

* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.threshold_eq_ceil`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsSparseSystem.incidences_le`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.threshold_le`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.threshold_le_pow`: the threshold and the
  number of scope incidences.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.length_branchVars_le`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.length_branchVars_le_div_sqrt_log`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsReducedBranch.le_two_mul`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.IsReducedBranch.length_enc_le`: few
  branching variables, and branches no larger than their parent.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.isSparseBranch_of_isReducedBranch`: the
  branching instance.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.count_eq_rootCount`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.count_eq_commonZeroCount`: exactness.
* `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.computableInPolyTime_threshold`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.computableInPolyTime_branchVars`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.computableInPolyTime_branchInput`,
  `Cslib.Complexity.SubexponentialSAT.IncidenceBranching.exists_count_certificate`: resources.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D, Lemma D.2 and
  the first paragraph of its proof (p. 54).
-/

namespace Cslib.Complexity.SubexponentialSAT.IncidenceBranching

open Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM

local notation "encSys" => encList (encList (encList encNat))

public section

/-! ### The threshold, the branching variables and the counter -/

/-- **The branching threshold `D* = max{1, ⌈N₀ / n⌉} ⌈√λ⌉` of Lemma D.2** (p. 54), for a system on
`n` variables with `N₀ = ∑_i |equationVars P_i|` scope incidences and `λ = ⌈log₂ n⌉`. It is the
§5.5 selector `ParameterCheck.heavyIncidenceCutoff` at `max 1 N₀`; see `threshold_eq_ceil`. -/
@[expose] def threshold (n : ℕ) (sys : List (List (List ℕ))) : ℕ :=
  ParameterCheck.heavyIncidenceCutoff (max 1 (sys.map fun eq => (equationVars eq).length).sum) n

/-- The branching variables of Lemma D.2: the variables `v < n` in more than `D*` scopes, in
increasing order. -/
@[expose] def branchVars (n : ℕ) (sys : List (List (List ℕ))) : List ℕ :=
  HeavyBranchFold.heavyVarList n (threshold n sys) sys

/-- The input `(n, S, sys)` of the streaming branching, with `S = branchVars n sys`. -/
@[expose] def branchInput (n : ℕ) (sys : List (List (List ℕ))) : HeavyBranchFold.BranchInput :=
  (n, branchVars n sys, sys)

/-- `(n', sys')` is a **reduced branch** of `(n, sys)`: fixing the branching variables to some
values leaves the nonempty system `sys'` on its `n'` relabeled free variables, without a
contradictory equation. -/
@[expose] def IsReducedBranch (n : ℕ) (sys : List (List (List ℕ))) (n' : ℕ)
    (sys' : List (List (List ℕ))) : Prop :=
  ∃ vals : List Bool, vals.length = (branchVars n sys).length ∧
    HeavyBranchFold.prepareBranch n (branchVars n sys) vals sys = .reduced n' sys'

/-- **The high-incidence branching of Lemma D.2.** Branch on every assignment to `branchVars n sys`,
call `solver` on each reduced branch, and add the branch counts. Contradictory branches count `0`,
and branches with no equation left count `2 ^ n'`. -/
@[expose] def count (solver : ℕ → List (List (List ℕ)) → ℕ) (n : ℕ) (sys : List (List (List ℕ))) :
    ℕ :=
  HeavyBranchFold.countByBranching solver (branchInput n sys)

/-- **The hypotheses of Lemma D.2** (p. 54) on a normalized system `sys` on `n` declared variables:
at most `c n` equations, each listing at most `⌈log₂ n⌉ ^ c` distinct monomials of degree at most
`k`. -/
structure IsSparseSystem (k c n : ℕ) (sys : List (List (List ℕ))) : Prop where
  /-- Every variable is declared: it is below `n`. -/
  vars_lt : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n
  /-- Every equation is normalized: strictly increasing, pairwise distinct monomials. -/
  canonical : ∀ eq ∈ sys, IsCanonicalEquation eq
  /-- At most `c n` equations. -/
  length_le : sys.length ≤ c * n
  /-- Every equation lists at most `⌈log₂ n⌉ ^ c` monomials. -/
  monomials_le : ∀ eq ∈ sys, eq.length ≤ Nat.clog 2 n ^ c
  /-- Every monomial has degree at most `k`. -/
  degree_le : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k

/-- **The hypotheses of the branch solver of Lemma D.2**: those of the lemma, together with scopes
of at most `⌈log₂ n⌉ ^ c` variables and every variable in at most `⌈log₂ n⌉ ^ c` scopes (p. 54). -/
structure IsSparseBranch (k c n : ℕ) (sys : List (List (List ℕ))) : Prop
    extends IsSparseSystem k c n sys where
  /-- Every scope has at most `⌈log₂ n⌉ ^ c` variables. -/
  scope_le : ∀ eq ∈ sys, (equationVars eq).length ≤ Nat.clog 2 n ^ c
  /-- Every variable lies in at most `⌈log₂ n⌉ ^ c` scopes. -/
  varDegree_le : ∀ v < n, varDegree v sys ≤ Nat.clog 2 n ^ c

end

/-! ### The threshold -/

/-- For `n ≥ 2`, `D* = ⌈max{1, N₀} / n⌉ (⌊√(λ - 1)⌋ + 1)` in natural numbers. -/
private theorem threshold_eq_mul {n : ℕ} (hn : 2 ≤ n) (sys : List (List (List ℕ))) :
    threshold n sys = max 1 (sys.map fun eq => (equationVars eq).length).sum ⌈/⌉ n *
      ((Nat.clog 2 n - 1).sqrt + 1) := by
  have hlam : Nat.clog 2 n ≠ 0 := (Nat.clog_pos Nat.one_lt_two (by omega)).ne'
  simp only [threshold, ParameterCheck.heavyIncidenceCutoff, hlam, ↓reduceIte,
    Nat.ceilDiv_eq_add_pred_div]

public section

/-- **`D*` is the threshold of the source** (p. 54): for `n ≥ 1`,
`threshold n sys = max{1, ⌈N₀ / n⌉} ⌈√λ⌉` with `N₀ = ∑_i |equationVars P_i|`. -/
theorem threshold_eq_ceil {n : ℕ} (hn : 1 ≤ n) (sys : List (List (List ℕ))) :
    threshold n sys =
      max 1 ⌈(((sys.map fun eq => (equationVars eq).length).sum : ℕ) : ℝ) / n⌉₊ *
        ⌈Real.sqrt (Nat.clog 2 n)⌉₊ := by
  rw [threshold, ParameterCheck.heavyIncidenceCutoff_eq_ceil_mul hn, Nat.ceil_div_eq_ceilDiv _ hn,
    Nat.ceil_div_eq_ceilDiv _ hn]
  congr 1
  set N := (sys.map fun eq => (equationVars eq).length).sum
  refine le_antisymm ((Nat.ceilDiv_le_iff hn).mpr (max_le ?_ ?_)) (max_le ?_ ?_)
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact (Nat.le_ceilDiv_mul hn).trans (Nat.mul_le_mul_right n (le_max_right 1 _))
  · simp only [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by have := le_max_left 1 N; omega) hn
  · simp only [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by have := le_max_right 1 N; omega)

/-- **Few branching variables** (p. 54): if every variable is below `n`, at most `n / ⌈√λ⌉`
variables lie in more than `D*` scopes, where `⌈√λ⌉ = ⌊√(λ - 1)⌋ + 1`. -/
theorem length_branchVars_le {n : ℕ} {sys : List (List (List ℕ))}
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    (branchVars n sys).length ≤ n / ((Nat.clog 2 n - 1).sqrt + 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hc : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one (by omega) 2
    rw [hc, Nat.zero_sub, Nat.sqrt_zero, Nat.div_one]
    exact (List.length_filter_le _ _).trans_eq List.length_range
  set N := (sys.map fun eq => (equationVars eq).length).sum
  set q := max 1 N ⌈/⌉ n
  set s := (Nat.clog 2 n - 1).sqrt + 1
  have hq_pos : 0 < q := by
    simp only [q, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by have := le_max_left 1 N; omega) (by omega)
  have hD : threshold n sys = q * s := threshold_eq_mul hn sys
  have hN : N ≤ q * n := (le_max_right 1 N).trans (Nat.le_ceilDiv_mul (by omega))
  calc (branchVars n sys).length ≤ N / threshold n sys :=
        HeavyBranchFold.length_heavyVarList_le_div (by rw [hD]; positivity) hvars
    _ ≤ (q * n) / (q * s) := by rw [hD]; exact Nat.div_le_div_right hN
    _ = n / s := Nat.mul_div_mul_left n s hq_pos

/-- **Few branching variables**, against `⌊√⌊log₂ n⌋⌋`: for `n ≥ 2`, at most
`n / ⌊√⌊log₂ n⌋⌋` variables lie in more than `D*` scopes. -/
theorem length_branchVars_le_div_sqrt_log {n : ℕ} {sys : List (List (List ℕ))} (hn : 2 ≤ n)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    (branchVars n sys).length ≤ n / Nat.sqrt (Nat.log 2 n) := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using hn)
  have hsqrt : 0 < Nat.sqrt (Nat.log 2 n) := Nat.sqrt_pos.mpr hlog
  exact (length_branchVars_le hvars).trans
    (Nat.div_le_div_left (Nat.sqrt_log_two_le_sqrt_clog_two_sub_one_add_one n) hsqrt)

/-- **The number of scope incidences** under the hypotheses of Lemma D.2:
`N₀ = ∑_i |I_i| ≤ c k λ^c n` (p. 54). -/
theorem IsSparseSystem.incidences_le {k c n : ℕ} {sys : List (List (List ℕ))}
    (h : IsSparseSystem k c n sys) :
    (sys.map fun eq => (equationVars eq).length).sum ≤ c * k * Nat.clog 2 n ^ c * n := by
  have hsum := List.sum_le_length_nsmul (sys.map fun eq => (equationVars eq).length)
    (k * Nat.clog 2 n ^ c) fun x hx => by
      obtain ⟨eq, heq, rfl⟩ := List.mem_map.mp hx
      exact (length_equationVars_le (h.degree_le eq heq)).trans
        (Nat.mul_le_mul_left k (h.monomials_le eq heq))
  rw [List.length_map, smul_eq_mul] at hsum
  calc _ ≤ sys.length * (k * Nat.clog 2 n ^ c) := hsum
    _ ≤ (c * n) * (k * Nat.clog 2 n ^ c) := Nat.mul_le_mul_right _ h.length_le
    _ = c * k * Nat.clog 2 n ^ c * n := by ring

/-- **`D*` is polylogarithmic** (p. 54): under the hypotheses of Lemma D.2,
`D* ≤ max{1, c k λ^c} ⌈√λ⌉`, with `⌈√λ⌉ = ⌊√(λ - 1)⌋ + 1`. -/
theorem threshold_le {k c n : ℕ} {sys : List (List (List ℕ))} (h : IsSparseSystem k c n sys) :
    threshold n sys ≤ max 1 (c * k * Nat.clog 2 n ^ c) * ((Nat.clog 2 n - 1).sqrt + 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hc : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one (by omega) 2
    simp only [threshold, ParameterCheck.heavyIncidenceCutoff, hc, ↓reduceIte, mul_zero,
      Nat.zero_le]
  rw [threshold_eq_mul hn]
  refine Nat.mul_le_mul_right _ ((Nat.div_lt_iff_lt_mul (by omega)).mpr ?_ |> Nat.le_of_lt_succ)
  set B := c * k * Nat.clog 2 n ^ c
  have hN := h.incidences_le
  have hmax : max 1 (sys.map fun eq => (equationVars eq).length).sum ≤ max 1 B * n := by
    refine max_le (Nat.one_le_iff_ne_zero.mpr (by positivity)) (hN.trans ?_)
    exact Nat.mul_le_mul_right n (le_max_right 1 B)
  have : 1 ≤ max 1 B := le_max_left 1 B
  rw [Nat.succ_mul]; omega

/-- **`D* ≤ λ ^ (c + 2)`** (p. 54): under the hypotheses of Lemma D.2, for `n ≥ 2` and
`c k ≤ λ`. -/
theorem threshold_le_pow {k c n : ℕ} {sys : List (List (List ℕ))} (h : IsSparseSystem k c n sys)
    (hn : 2 ≤ n) (hck : c * k ≤ Nat.clog 2 n) : threshold n sys ≤ Nat.clog 2 n ^ (c + 2) := by
  set lam := Nat.clog 2 n
  have hlam : 1 ≤ lam := Nat.clog_pos Nat.one_lt_two (by omega)
  have hmax : max 1 (c * k * lam ^ c) ≤ lam ^ (c + 1) := by
    refine max_le (Nat.one_le_pow _ _ (by omega)) ?_
    rw [pow_succ']
    exact Nat.mul_le_mul_right _ hck
  have hs : (lam - 1).sqrt + 1 ≤ lam := by
    have := Nat.sqrt_le_self (lam - 1); omega
  calc threshold n sys ≤ max 1 (c * k * lam ^ c) * ((lam - 1).sqrt + 1) := threshold_le h
    _ ≤ lam ^ (c + 1) * lam := Nat.mul_le_mul hmax hs
    _ = lam ^ (c + 2) := (pow_succ lam (c + 1)).symm

/-! ### Reduced branches -/

/-- **A reduced branch keeps at least half the variables** (p. 54): for `n ≥ 3` and every variable
below `n`, it has `n' = n - |S|` free variables and `n ≤ 2 n'`. -/
theorem IsReducedBranch.le_two_mul {n n' : ℕ} {sys sys' : List (List (List ℕ))} (hn : 3 ≤ n)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (hb : IsReducedBranch n sys n' sys') :
    n' = n - (branchVars n sys).length ∧ n ≤ 2 * n' := by
  obtain ⟨vals, -, hred⟩ := hb
  have hn' := HeavyBranchFold.prepareBranch_freeVars_eq.2 sys' hred
  have hlam : 2 ≤ Nat.clog 2 n := by
    have := Nat.clog_mono_right 2 hn
    rwa [show Nat.clog 2 3 = 2 by decide] at this
  have hs : 2 ≤ (Nat.clog 2 n - 1).sqrt + 1 := by
    have := Nat.sqrt_pos.mpr (by omega : 0 < Nat.clog 2 n - 1); omega
  have hS := (length_branchVars_le hvars).trans (Nat.div_le_div_left hs (by norm_num))
  have := Nat.div_mul_le_self n 2
  exact ⟨hn', by omega⟩

/-- A reduced branch is no longer to encode than its parent system, so bounds on the branch solver
in the encoded length of the branch transfer to the parent input. -/
theorem IsReducedBranch.length_enc_le {n n' : ℕ} {sys sys' : List (List (List ℕ))}
    (hb : IsReducedBranch n sys n' sys') :
    (encPair encUnary encSys (n', sys')).length ≤ (encPair encUnary encSys (n, sys)).length := by
  obtain ⟨_, -, hred⟩ := hb
  exact HeavyBranchFold.length_enc_reduced_le_parent hred

/-- **The branching instance of Lemma D.2** (p. 54). Under the hypotheses of the lemma, for
`n ≥ 5` and `2 ^ ((c + 1) k) ≤ n`, every reduced branch `(n', sys')` satisfies the branch solver's
hypotheses at its own variable count, with the explicit constant `2 c + 4`:
at most `(2c + 4) n'` equations, and at most `⌈log₂ n'⌉ ^ (2c + 4)` monomials per equation,
variables per scope and scopes per variable. Also `n ≤ 2 n'`. -/
theorem isSparseBranch_of_isReducedBranch {k c n n' : ℕ} {sys sys' : List (List (List ℕ))}
    (h : IsSparseSystem k c n sys) (hn : 5 ≤ n) (hk : 2 ^ ((c + 1) * k) ≤ n)
    (hb : IsReducedBranch n sys n' sys') : IsSparseBranch k (2 * c + 4) n' sys' ∧ n ≤ 2 * n' := by
  obtain ⟨-, hn2⟩ := hb.le_two_mul (by omega) h.vars_lt
  obtain ⟨vals, -, hred⟩ := hb
  set S := branchVars n sys
  have hS_nd : S.Nodup := HeavyBranchFold.nodup_heavyVarList _ _ _
  have hSn : ∀ s ∈ S, s < n := fun _ hs => HeavyBranchFold.lt_of_mem_heavyVarList hs
  obtain ⟨-, -, -, -, hcan', hvars'⟩ :=
    HeavyBranchFold.prepareBranch_reduced_canonical hS_nd hSn h.canonical h.vars_lt hred
  obtain ⟨hlen', hshrink⟩ := HeavyBranchFold.prepareBranch_reduced_length_le hred
  set lam := Nat.clog 2 n
  set lam' := Nat.clog 2 n'
  have hlam'2 : 2 ≤ lam' := by
    have := Nat.clog_mono_right 2 (by omega : 3 ≤ n')
    rwa [show Nat.clog 2 3 = 2 by decide] at this
  have hlam_sq : lam ≤ lam' ^ 2 :=
    (Nat.clog_two_le_two_mul_of_le_two_mul hn2 (by omega)).trans (by nlinarith)
  have htransfer {α : ℕ} (hα : 2 * α ≤ 2 * c + 4) : lam ^ α ≤ lam' ^ (2 * c + 4) :=
    (Nat.pow_le_pow_left hlam_sq α).trans
      ((pow_mul lam' 2 α).symm.trans_le (Nat.pow_le_pow_right (by omega) hα))
  have hk_lam : (c + 1) * k ≤ lam := by
    have := Nat.clog_mono_right 2 hk; rwa [Nat.clog_pow 2 _ Nat.one_lt_two] at this
  refine ⟨⟨⟨hvars', hcan', ?_, fun eq' heq' => ?_,
    HeavyBranchFold.prepareBranch_reduced_degree_le h.degree_le hred⟩, fun eq' heq' => ?_,
    fun u hu => ?_⟩, hn2⟩
  · calc sys'.length ≤ sys.length := hlen'
      _ ≤ c * n := h.length_le
      _ ≤ c * (2 * n') := Nat.mul_le_mul_left c hn2
      _ ≤ (2 * c + 4) * n' := by nlinarith
  · obtain ⟨eq, heq, hl, -⟩ := hshrink eq' heq'
    exact (hl.trans (h.monomials_le eq heq)).trans (htransfer (by omega))
  · obtain ⟨eq, heq, -, hsc⟩ := hshrink eq' heq'
    have hscope : (equationVars eq).length ≤ lam ^ (c + 1) :=
      (length_equationVars_le (h.degree_le eq heq)).trans
        ((Nat.mul_le_mul_left k (h.monomials_le eq heq)).trans (by
          rw [pow_succ']
          exact Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_left k (Nat.succ_pos c)).trans hk_lam)))
    exact (hsc.trans hscope).trans (htransfer (by omega))
  · have hinc := HeavyBranchFold.prepareBranch_reduced_varDegree_le hS_nd hSn
      (fun u hun huS => HeavyBranchFold.varDegree_le_of_not_mem_heavyVarList hun huS) hred u hu
    exact (hinc.trans (threshold_le_pow h (by omega) (by nlinarith))).trans
      (htransfer (by omega))

/-! ### Exactness -/

/-- **Exactness of the branching** (p. 54): if every variable is below `n` and `solver` counts the
common zeros of every reduced branch, `count solver n sys` counts those of `sys`. -/
theorem count_eq_rootCount {solver : ℕ → List (List (List ℕ)) → ℕ} {n : ℕ}
    {sys : List (List (List ℕ))} (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hsolver : ∀ n' sys', IsReducedBranch n sys n' sys' →
      solver n' sys' = HeavyBranchFold.rootCount n' sys') :
    count solver n sys = HeavyBranchFold.rootCount n sys :=
  HeavyBranchFold.countByBranching_eq_rootCount (HeavyBranchFold.nodup_heavyVarList _ _ _)
    (fun _ hs => HeavyBranchFold.lt_of_mem_heavyVarList hs) hvars
    fun vals hlen n' sys' hred => hsolver n' sys' ⟨vals, hlen, hred⟩

/-- **Exactness against `commonZeroCount`**: for a normalized system on `n` variables, the counter
returns the number of common zeros of the equations `toFinsetEquation n sys[i]` on `Fin n`. -/
theorem count_eq_commonZeroCount {solver : ℕ → List (List (List ℕ)) → ℕ} {n : ℕ}
    {sys : List (List (List ℕ))} (hcan : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hsolver : ∀ n' sys', IsReducedBranch n sys n' sys' →
      solver n' sys' = HeavyBranchFold.rootCount n' sys') :
    count solver n sys = commonZeroCount Finset.univ
      (fun i : Fin sys.length => HeavyBranchFold.toFinsetEquation n sys[i]) := by
  rw [count_eq_rootCount hvars hsolver, HeavyBranchFold.rootCount_eq_commonZeroCount hcan hvars]

end

/-! ### Resources -/

section PolyTime

open ComputableInPolyTime

local notation "CPT" => ComputableInPolyTime

private theorem computableInPolyTime_incidences :
    CPT (fun p : ℕ × List (List (List ℕ)) =>
        max 1 (p.2.map fun eq => (equationVars eq).length).sum)
      (encPair encUnary encSys) encNat := by
  have hlen : CPT (fun eq : List (List ℕ) => (equationVars eq).length)
      (encList (encList encNat)) encNat :=
    unary_to_binary.comp ((length_list encNat).comp computableInPolyTime_equationVars)
  have hlist : CPT (fun p : ℕ × List (List (List ℕ)) =>
      p.2.map fun eq => (equationVars eq).length) (encPair encUnary encSys) (encList encNat) :=
    mapWithInput (snd encUnary encSys) (hlen.comp (snd _ _))
  have hsum := (show CPT List.sum (encList encNat) encNat by fun_prop).comp hlist
  have hmax1 : CPT (fun x : ℕ => max 1 x) encNat encNat :=
    ((binary_le' (const 1) id').ite' id' (const 1)).of_enc_eq fun x =>
      congrArg encNat (by split_ifs with hx <;> simp only [decide_eq_true_eq] at hx <;> omega)
  exact hmax1.comp hsum

public section

/-- **`D*` is polynomial-time** (`n` in unary, the result in binary). -/
@[fun_prop]
theorem computableInPolyTime_threshold :
    CPT (fun p : ℕ × List (List (List ℕ)) => threshold p.1 p.2)
      (encPair encUnary encSys) encNat :=
  ParameterCheck.computableInPolyTime_heavyIncidenceCutoff_apply computableInPolyTime_incidences
    (unary_to_binary.comp (fst encUnary encSys))

/-- The branching variables are polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_branchVars :
    CPT (fun p : ℕ × List (List (List ℕ)) => branchVars p.1 p.2)
      (encPair encUnary encSys) (encList encNat) :=
  HeavyBranchFold.computableInPolyTime_heavyVarList_comp (fst encUnary encSys)
    computableInPolyTime_threshold (snd encUnary encSys)

/-- The input of the streaming branching is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_branchInput :
    CPT (fun p : ℕ × List (List (List ℕ)) => branchInput p.1 p.2)
      (encPair encUnary encSys) HeavyBranchFold.encBranchInput := by
  unfold HeavyBranchFold.encBranchInput
  exact (fst encUnary encSys).prod (computableInPolyTime_branchVars.prod (snd encUnary encSys))

end

end PolyTime

/-- The largest cost of a solver over the reduced branches of `branchInput n sys` is at most any
bound on its cost on the reduced branches of `(n, sys)`. -/
public theorem maxReducedCost_branchInput_le {cost : ℕ × List (List (List ℕ)) → ℕ} {n : ℕ}
    {sys : List (List (List ℕ))} {B : ℕ}
    (hB : ∀ n' sys', IsReducedBranch n sys n' sys' → cost (n', sys') ≤ B) :
    HeavyBranchFold.maxReducedCost cost (branchInput n sys) ≤ B :=
  HeavyBranchFold.maxReducedCost_le fun _ _ n' sys' hout =>
    hB n' sys' ⟨_, length_lowBits _ _, hout⟩

public section

/-- **Resources of the high-incidence branching** (p. 54). There is `K` such that, for every
solver bounded by `2 ^ n'` and every certificate for it, the counter has a certificate with the
following bounds. On an input `x = (n, sys)` whose reduced branches the solver handles in time at
most `R` and space at most `Q`, the time is at most `(2 ^ |S| + 1) (K (|x| + 1) ^ K + R)`, with
`S = branchVars n sys`, and the space is at most `K (|x| + 1) ^ K + Q`. Here `|x|` is the encoded
length of the input. With `length_branchVars_le`, `2 ^ |S| ≤ 2 ^ (n / ⌈√λ⌉)`. -/
theorem exists_count_certificate :
    ∃ K : ℕ, ∀ (solver : ℕ → List (List (List ℕ)) → ℕ)
      (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
        (encPair encUnary encSys) encNat),
      (∀ n' sys', solver n' sys' ≤ 2 ^ n') →
      ∃ cs : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => count solver p.1 p.2)
          (encPair encUnary encSys) encNat,
        ∀ (n : ℕ) (sys : List (List (List ℕ))) (R Q : ℕ),
          (∀ n' sys', IsReducedBranch n sys n' sys' →
            csolver.time (n', sys') ≤ R ∧ csolver.space (n', sys') ≤ Q) →
          cs.time (n, sys) ≤ (2 ^ (branchVars n sys).length + 1) *
              (K * ((encPair encUnary encSys (n, sys)).length + 1) ^ K + R) ∧
            cs.space (n, sys) ≤ K * ((encPair encUnary encSys (n, sys)).length + 1) ^ K + Q := by
  have hPrep := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_branchInput
  have hstep : PolyBounded (fun p : ℕ × List (List (List ℕ)) => (encPair encUnary encSys p).length)
      (fun p => HeavyBranchFold.stepOverhead
        (HeavyBranchFold.encBranchInput (branchInput p.1 p.2)).length) :=
    (PolyBounded.of_polynomiallyBounded _ HeavyBranchFold.polynomiallyBounded_stepOverhead).comp
      computableInPolyTime_branchInput.polyBounded_length
  obtain ⟨C, d, hCd⟩ := ((hPrep.1.add hPrep.2).add (hstep.add hstep)).exists_le
  refine ⟨C + d, fun solver csolver hbound => ?_⟩
  have hc := HeavyBranchFold.countByBranching_computableInO csolver
    (HeavyBranchFold.maxReducedCost csolver.time) (HeavyBranchFold.maxReducedCost csolver.space)
    (fun _ _ _ n' sys' _ => hbound n' sys')
    (fun _ _ hidx _ _ hred => HeavyBranchFold.le_maxReducedCost csolver.time hidx hred)
    (fun _ _ hidx _ _ hred => HeavyBranchFold.le_maxReducedCost csolver.space hidx hred)
  let cBr : NativeCertificate (HeavyBranchFold.countByBranching solver)
      HeavyBranchFold.encBranchInput encNat := ⟨_, _, hc⟩
  refine ⟨(cBr.comp (NativeCertificate.ofPolyTime computableInPolyTime_branchInput)).congr
    fun _ => rfl, fun n sys R Q hRQ => ?_⟩
  have hR := maxReducedCost_branchInput_le (cost := csolver.time) fun n' sys' h =>
    (hRQ n' sys' h).1
  have hQ := maxReducedCost_branchInput_le (cost := csolver.space) fun n' sys' h =>
    (hRQ n' sys' h).2
  have hbase := hCd (n, sys)
  have hpow : C * ((encPair encUnary encSys (n, sys)).length + 1) ^ d ≤
      (C + d) * ((encPair encUnary encSys (n, sys)).length + 1) ^ (C + d) :=
    Nat.mul_le_mul (Nat.le_add_right C d)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left d C))
  have h1 : 1 ≤ 2 ^ (branchVars n sys).length := Nat.one_le_two_pow
  -- The time is preprocessing, then the streaming loop over the `2 ^ |S|` branches.
  let L := (HeavyBranchFold.encBranchInput (branchInput n sys)).length
  change (NativeCertificate.ofPolyTime computableInPolyTime_branchInput).time (n, sys) +
      (HeavyBranchFold.stepOverhead L + (2 ^ (branchVars n sys).length + 1) *
        (HeavyBranchFold.stepOverhead L +
          HeavyBranchFold.maxReducedCost csolver.time (branchInput n sys))) ≤ _ ∧
    (NativeCertificate.ofPolyTime computableInPolyTime_branchInput).space (n, sys) +
      (HeavyBranchFold.stepOverhead L +
        HeavyBranchFold.maxReducedCost csolver.space (branchInput n sys)) ≤ _
  generalize (NativeCertificate.ofPolyTime computableInPolyTime_branchInput).time (n, sys) = A
    at hbase ⊢
  generalize (NativeCertificate.ofPolyTime computableInPolyTime_branchInput).space (n, sys) = B
    at hbase ⊢
  generalize HeavyBranchFold.stepOverhead L = T at hbase ⊢
  generalize 2 ^ (branchVars n sys).length = E at h1 ⊢
  have hmul := Nat.mul_le_mul_left (E + 1) (Nat.add_le_add_left hR T)
  constructor
  · nlinarith
  · omega

end

end Cslib.Complexity.SubexponentialSAT.IncidenceBranching
