/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.AntiChecker.Generator
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy

/-!
# Oracle circuits for Gap-MCSP from the anti-checker generator

[Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam, Proposition 63, sixth bullet]
[ChenHiraharaOliveiraPichRajgopalSanthanam2020] reads [Oliveira, Pich and Santhanam]
[OliveiraPichSanthanam2019] as an oracle circuit: for `s(n) ≤ 2 ^ n / poly(n)`, Gap-MCSP has
oracle circuits with `N · poly(s)` gates, of which `N · poly(s)` are oracle gates, each of fan-in
`poly(s)`, with `poly(s)` oracle gates on any path, where `N = 2 ^ n`
([Chen et al., Definition 11][ChenHiraharaOliveiraPichRajgopalSanthanam2020]).

`Cslib.MCSP.exists_oracleCircuit_gapMCSP` is this bullet with explicit parameters and constants.
The circuit runs the anti-checker generator (`Cslib.MCSP.AntiChecker.generator`) for circuits with
at most `s₁` gates on the truth table of `f`, then makes one more query: whether some function with
at most `s₁` gates agrees with `f` on all the chosen samples, which the oracle answers at power `1`
and threshold `0`
(`Cslib.MCSP.AntiChecker.encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff`).
The circuit outputs the negation of that answer. With the oracle `antiCheckerOracle`, every sample
is a correct pair `(y, f y)`, so a yes-instance (complexity at most `s₁`) is accepted. When `f`
needs more gates than `n` circuits with `s₁` gates and their strict majority, which holds for the
no-instances once `n s₁ + 2 + 2 n (n + 2) ≤ s₂`, the samples are an anti-checker, so no function
with `s₁` gates agrees with them and `f` is rejected. One fixed oracle answers both the generator's
queries and the final query, as Definition 11 (iii) requires.

The statement is unconditional, and its gap is explicit. The bullet's `s` is `s₂` here. The
statement differs from the source in three ways. The first drops a uniformity condition, the
second drops a size restriction, and the third is a difference of presentation:
* "constructive" is dropped: the circuits are nonuniform, so `s₁` and `s₂` are arbitrary;
* `s ≤ 2 ^ n / poly(n)` is not needed: the bounds hold for every `s₂` above the gap;
* the class `[q, ℓ, a]–Circuit[·]` of Definition 11 is not defined here. The four bounds are stated
  directly: size, oracle-gate count (`Program.cost` with `OracleOp.queryWeight`), fan-in
  (`Circuit.FanInAtMost`) and oracle depth (`Circuit.depthWith`).

Source locator: ECCC TR19-168, Appendix A.2, Proposition 63, sixth bullet (p. 52).

## Main results

* `Cslib.MCSP.exists_oracleCircuit_gapMCSP`: Gap-MCSP oracle circuits with `5000 N s₂ ^ 5` gates,
  at most `610 N s₂ ^ 4 + 1` oracle gates, each of fan-in at most `5000 s₂ ^ 5`, and at most
  `610 s₂ ^ 4 + 1` oracle gates on any path, under the oracle `antiCheckerOracle`.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean AntiChecker Turing.MultiTapeTM

variable {n : ℕ}

/-- The sources of the final query: the samples in the blocks of `R` rounds, at power `1` and
threshold `0`. -/
private def finalSources (s R : ℕ) : List (Source (2 ^ n + (n + 1) * R)) :=
  querySources n s 1 0 (List.ofFn fun j : Fin R => blockSources j)

private theorem length_finalSources (s R : ℕ) :
    (finalSources (n := n) s R).length = queryLength n s 1 0 R :=
  length_querySources_blockSources s 1 0 R

/-- **The final query**: whether no function with at most `s` gates agrees with the samples in the
blocks, as an oracle circuit on an output of the generator. -/
private def finalQuery (s R : ℕ) : Circuit oracleSignature (2 ^ n + (n + 1) * R) 1 :=
  (Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not) fun _ => 0).comp
    ((queryLayer fun _ : Fin 1 => fun a : Fin (queryLength n s 1 0 R) =>
        (finalSources (n := n) s R).get (a.cast (length_finalSources s R).symm)).comp
      (constLayer _))

private theorem eval_finalQuery (O : Language Bool) (s R : ℕ)
    (z : BitString (2 ^ n + (n + 1) * R)) :
    (finalQuery s R).eval (oracleInterpretation O) z 0 = true ↔
      encQuery (Query.ofSamples n s 1 0 (samplesOf z)) ∉ O := by
  have hofFn : List.ofFn (substitute (fun a : Fin (queryLength n s 1 0 R) =>
      (finalSources (n := n) s R).get (a.cast (length_finalSources s R).symm)) z) =
        encQuery (Query.ofSamples n s 1 0 (samplesOf z)) := by
    rw [← map_querySources_blockSources z s 1 0]
    apply List.ext_getElem
    · simp [length_querySources_blockSources]
    · intro a h₁ h₂
      simp only [finalSources, List.get_eq_getElem, List.getElem_ofFn, substitute,
        List.getElem_map]
      rfl
  simp only [finalQuery, Circuit.eval_comp, Circuit.eval_oneGate, oracleInterpretation_base,
    eval_queryLayer]
  change (!O.slice _ _) = true ↔ _
  rw [Bool.not_eq_true', ← Bool.not_eq_true, Language.slice_eq_true_iff, hofFn]

private theorem size_finalQuery (s R : ℕ) : (finalQuery (n := n) s R).size = 4 := by
  simp [finalQuery]

private theorem cost_finalQuery (s R : ℕ) :
    (finalQuery (n := n) s R).program.cost OracleOp.queryWeight = 1 := by
  rw [finalQuery, Circuit.cost_program_comp, Circuit.cost_program_comp, cost_program_constLayer,
    cost_program_queryLayer, Circuit.cost_program_oneGate]
  rfl

private theorem depthWith_finalQuery_le (s R : ℕ) :
    (finalQuery (n := n) s R).depthWith OracleOp.queryWeight ≤ 1 := by
  refine (Circuit.depthWith_comp_le _ _ _).trans ?_
  rw [Circuit.depthWith_oneGate, OracleOp.queryWeight_base, Nat.zero_add]
  refine (Circuit.depthWith_comp_le _ _ _).trans ?_
  rw [depthWith_constLayer, Nat.add_zero]
  exact depthWith_queryLayer_le _

private theorem fanInAtMost_finalQuery (s R : ℕ) {r : ℕ} (hr : queryLength n s 1 0 R ≤ r)
    (h1 : 1 ≤ r) : (finalQuery (n := n) s R).FanInAtMost r :=
  ((Circuit.fanInAtMost_oneGate _ _ _).2 h1).comp
    (((fanInAtMost_queryLayer _).mono hr).comp (fanInAtMost_constLayer _ _))

/-- **Gap-MCSP has efficient oracle circuits** [Chen, Hirahara, Oliveira, Pich, Rajgopal and
Santhanam, Proposition 63, sixth bullet][ChenHiraharaOliveiraPichRajgopalSanthanam2020] (from
[Oliveira, Pich and Santhanam][OliveiraPichSanthanam2019]). For thresholds with
`n s₁ + 2 + 2 n (n + 2) ≤ s₂` at length `n`, there is an oracle circuit on `2 ^ n` inputs with at
most `5000 · 2 ^ n · s₂ ^ 5` gates, at most `2 ^ n · 610 s₂ ^ 4 + 1` oracle gates, each gate of
fan-in at most `5000 s₂ ^ 5`, and at most `610 s₂ ^ 4 + 1` oracle gates on any path, which with the
oracle `antiCheckerOracle` accepts the yes-instances of `Gap-MCSP[s₁, s₂]` and rejects its
no-instances. -/
theorem exists_oracleCircuit_gapMCSP {s₁ s₂ : ℕ → ℕ} {n : ℕ}
    (hgap : n * s₁ n + 2 + 2 * n * (n + 2) ≤ s₂ n) :
    ∃ E : Circuit oracleSignature (2 ^ n) 1,
      E.size ≤ 5000 * 2 ^ n * s₂ n ^ 5 ∧
      E.program.cost OracleOp.queryWeight ≤ 2 ^ n * (610 * s₂ n ^ 4) + 1 ∧
      E.FanInAtMost (5000 * s₂ n ^ 5) ∧
      E.depthWith OracleOp.queryWeight ≤ 610 * s₂ n ^ 4 + 1 ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        E.eval (oracleInterpretation antiCheckerOracle) T 0 = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        E.eval (oracleInterpretation antiCheckerOracle) T 0 = false) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- At length `0` every function is constant, so there are no no-instances.
    have hs₂ : 2 ≤ s₂ 0 := by simpa using hgap
    refine ⟨Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const true)) Fin.elim0,
      ?_, ?_, ?_, ?_, fun _ _ => rfl, fun T hT => ?_⟩
    · rw [Circuit.size_oneGate]
      have : 1 ≤ s₂ 0 ^ 5 := Nat.one_le_pow _ _ (by omega)
      omega
    · rw [Circuit.cost_program_oneGate]
      exact Nat.zero_le _
    · exact (Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _)
    · rw [Circuit.depthWith_oneGate]
      exact Nat.zero_le _
    · exfalso
      rw [GapMCSP.ofFn_mem_noSet_iff] at hT
      have hconst : (truthTable 0).symm T = fun _ => (truthTable 0).symm T default :=
        funext fun x => congrArg _ (Subsingleton.elim x default)
      rw [hconst, complexity_const] at hT
      omega
  set s := s₁ n
  set R := antiCheckerRounds n s
  set ℓ := antiCheckerPower n s
  have hm : n + s + 1 ≤ s₂ n := by nlinarith
  set m := s₂ n
  have hR : R ≤ 610 * m ^ 4 :=
    (antiCheckerRounds_le n s).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 4))
  have hq : queryLength n s ℓ R R ≤ 5000 * m ^ 5 :=
    (queryLength_antiChecker_le n s).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 5))
  have hm1 : 1 ≤ m := by omega
  refine ⟨(finalQuery s R).comp (generator n s ℓ R), ?_, ?_, ?_, ?_, fun T hT => ?_, fun T hT => ?_⟩
  · -- Size.
    rw [Circuit.size_comp, size_finalQuery, size_generator]
    have h7 : 2 + 2 ^ n * (3 * n + 5) ≤ 2 ^ n * (7 * m) := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      nlinarith
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hm4 : 1 ≤ m ^ 4 := Nat.one_le_pow _ _ hm1
    calc R * (2 + 2 ^ n * (3 * n + 5)) + 4
        ≤ 610 * m ^ 4 * (2 ^ n * (7 * m)) + 4 * (2 ^ n * m ^ 5) := by
          gcongr
          nlinarith [Nat.one_le_pow 5 m hm1]
      _ = 4274 * 2 ^ n * m ^ 5 := by ring
      _ ≤ 5000 * 2 ^ n * m ^ 5 := by gcongr; norm_num
  · -- Oracle gates.
    rw [Circuit.cost_program_comp, cost_generator, cost_finalQuery]
    calc R * 2 ^ n + 1 ≤ 610 * m ^ 4 * 2 ^ n + 1 := by gcongr
      _ = 2 ^ n * (610 * m ^ 4) + 1 := by ring
  · -- Fan-in.
    have hq₀ : queryLength n s 1 0 R ≤ queryLength n s ℓ R R :=
      queryLength_mono (antiCheckerPower_pos n s) (Nat.zero_le R) le_rfl
    exact (fanInAtMost_finalQuery s R (hq₀.trans hq) (by nlinarith [Nat.one_le_pow 5 m hm1])).comp
      ((fanInAtMost_generator n s ℓ R).mono hq)
  · -- Oracle depth.
    refine (Circuit.depthWith_comp_le _ _ _).trans ?_
    have := depthWith_generator_le n s ℓ R
    have := depthWith_finalQuery_le (n := n) s R
    omega
  · -- Yes-instances: `f` itself agrees with every sample.
    rw [GapMCSP.ofFn_mem_yesSet_iff] at hT
    set f := (truthTable n).symm T
    have hTf : T = truthTable n f := (Equiv.apply_symm_apply _ T).symm
    rw [Circuit.eval_comp, eval_finalQuery, hTf,
      encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff]
    exact ⟨f, mem_computableFunctions_iff_complexity_le.2 hT,
      fun p hp => (snd_eq_of_mem_samplesOf_eval_generator _ n s ℓ R f hp).symm⟩
  · -- No-instances: the samples are an anti-checker, so no function with `s₁` gates agrees.
    rw [GapMCSP.ofFn_mem_noSet_iff] at hT
    set f := (truthTable n).symm T
    have hTf : T = truthTable n f := (Equiv.apply_symm_apply _ T).symm
    have hf : n * s + complexity interpretation (single (strictMajority n)) <
        complexity interpretation (single f) := by
      have := complexity_threshold_le n (n / 2 + 1)
      rw [strictMajority]
      nlinarith
    rw [Bool.eq_false_iff, Ne, Circuit.eval_comp, eval_finalQuery, hTf,
      encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff]
    rintro ⟨g, hg, hagree⟩
    obtain ⟨x, hx, hgx⟩ := isAntiChecker_samplesOf_generator hn (fun _ => Iff.rfl) hf g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hgx ((hagree p hp).trans (snd_eq_of_mem_samplesOf_eval_generator _ n s ℓ R f hp))

end Cslib.MCSP
