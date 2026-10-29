/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingTreeBound
public import Complexity.Computability.Complexity.FineGrained.CountingSparsifyContext
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Uniform resources for counting sparsification

Resource composition for the existing captured-context search. The threshold and leaf machines
are fixed before the runtime context and formula. The original occurring-support accumulator is
retained; the declared-variable wrapper applies its final correction exactly once.

The polynomial numerical-depth premise is explicit. A short binary parameter encoding alone does
not establish that premise. This module does not construct the leaf counter or establish the final
subexponential counting endpoint of [OpenAI2026ETH], Section 6.4 (pp. 43–44).

## Main results

* `Cslib.Complexity.CountingSparsify.computableInPolyTime_roundsWith`: the binary loop clock
  with a runtime binary divisor, without materializing the number of rounds in unary.
* `Cslib.Complexity.CountingSparsify.exists_computableInO_normalizeDeclaredLeaf`: independent
  time and workspace for exact leaf normalization, charging the intermediate declared count.
* `Cslib.Complexity.CountingSparsify.length_encNat_searchDeclaredWith_le`: the final output
  occupies at most the externally declared count plus one bits.
* `Cslib.Complexity.CountingSparsify.exists_computableInO_searchDeclaredWith`: one plain search
  certificate on the full context, unary declared size and formula, with independent resources.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4 and Appendix A.
-/

@[expose] public section

namespace Cslib.Complexity.CountingSparsify

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open Cslib.Logic.PL.CNF (validDeclaredInput validDeclaredInput_eq_true_iff normalizeDeclaredLeaf)

variable {P : Type} {encP : P ↪ List Bool}

private theorem input_formula_size :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => (encCNF x.2).length) :=
  PolyBounded.self.mono fun x => length_le_encPair_right encP encCNF x

private theorem input_context_size :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => (encP x.1).length) :=
  PolyBounded.self.mono fun x => length_le_encPair_left encP encCNF x

private theorem input_numVars :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => x.2.numVars) :=
  input_formula_size.mono fun x => x.2.numVars_le_length_vars.trans (SAT.length_vars_le x.2)

private theorem nodeBound_runtime_polyBounded (K : ℕ) {D : P → ℕ}
    (hD : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => D x.1)) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => nodeBound K (D x.1) x.2) := by
  have hm := input_formula_size (encP := encP) |>.mono
    (fun x => length_le_length_encList _ x.2)
  exact ((hm.add (.const 1)).add ((PolyBounded.const K).mul (hD.mul input_numVars))).mul
    (((PolyBounded.const 2).mul ((PolyBounded.const K).mul
      (((PolyBounded.const 2).mul input_formula_size).add (.const 1)))).add (.const 1))

private theorem stateBound_runtime_polyBounded (K : ℕ) {D : P → ℕ}
    (hD : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => D x.1)) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => stateBound K (D x.1) x.2) := by
  have hstack := ((hD.mul input_numVars).add (.const 1)).mul
    (((PolyBounded.const 2).mul (nodeBound_runtime_polyBounded K hD)).add (.const 1))
  exact (((PolyBounded.const 4).mul input_numVars).add
    ((PolyBounded.const 4).mul hstack)).add (.const 10)

private theorem contextStateBound_polyBounded (K : ℕ) {D : P → ℕ}
    (hD : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => D x.1)) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => 2 * (encP x.1).length + 1 + stateBound K (D x.1) x.2) :=
  (((PolyBounded.const 2).mul input_context_size).add (.const 1)).add
    (stateBound_runtime_polyBounded K hD)

private theorem computableInPolyTime_init_uniform (k : ℕ) :
    ComputableInPolyTime (fun x : P × CNF ℕ => (x.1, init k x.2))
      (encPair encP encCNF) (encPair encP encState) := by
  have hinit : ComputableInPolyTime (init k) encCNF encState := by
    have hnorm := computableInPolyTime_countingNormalize encNat
    unfold init root encState encCNF
    fun_prop
  exact (ComputableInPolyTime.fst encP encCNF).prod
    (hinit.comp (ComputableInPolyTime.snd encP encCNF))

private theorem div_min_succ (m b : ℕ) : m / min (m + 1) b = m / b := by
  by_cases h : b ≤ m + 1
  · rw [min_eq_right h]
  · rw [min_eq_left (by omega), Nat.div_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega)]

/-- Compute the existing search clock with a runtime binary divisor. Saturating the divisor at
the unary support size plus one preserves the quotient, so no unary exponential is produced. -/
theorem computableInPolyTime_roundsWith {BOf : P → ℕ}
    (hB : ComputableInPolyTime BOf encP encNat) :
    ComputableInPolyTime (fun x : P × CNF ℕ => rounds (BOf x.1) x.2)
      (encPair encP encCNF) encNat := by
  have hm : ComputableInPolyTime (fun x : P × CNF ℕ => x.2.distinctVars.length)
      (encPair encP encCNF) encUnary := by fun_prop
  have hb := hB.comp (ComputableInPolyTime.fst encP encCNF)
  have hcap := ComputableInPolyTime.binary_min_unary'
    (show ComputableInPolyTime (fun x : P × CNF ℕ => x.2.distinctVars.length + 1)
      (encPair encP encCNF) encUnary by fun_prop) hb
  have hdiv := ComputableInPolyTime.unary_div.comp (hm.prod hcap)
  have hpow := ComputableInPolyTime.binary_two_pow.comp
    (show ComputableInPolyTime
      (fun x : P × CNF ℕ => x.2.distinctVars.length /
        min (x.2.distinctVars.length + 1) (BOf x.1) + 2)
      (encPair encP encCNF) encUnary by fun_prop)
  convert hpow using 1
  funext x
  simp only [Function.comp_apply, rounds, div_min_succ]

private theorem rounds_length_polyBounded (BOf : P → ℕ) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => (encNat (rounds (BOf x.1) x.2)).length) := by
  refine (input_numVars.add (.const 3)).mono fun x => ?_
  rw [rounds, CNF.length_distinctVars, encNat_two_pow, List.length_append,
    List.length_replicate, List.length_singleton]
  have := Nat.div_le_self x.2.numVars (BOf x.1)
  omega

private theorem computableInPolyTime_validDeclaredInput_uniform (k : ℕ) {NOf : P → ℕ}
    (hN : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => validDeclaredInput k (NOf x.1) x.2)
      (encPair encP encCNF) encBool := by
  have hNbin := ComputableInPolyTime.unary_to_binary.comp hN
  have hlt : ComputableInPolyTime
      (fun x : (P × CNF ℕ) × ℕ => decide (x.2 < NOf x.1.1))
      (encPair (encPair encP encCNF) encNat) encBool :=
    ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.snd _ _).prod
        (hNbin.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))))
  have hs : ComputableInPolyTime
      (fun x : P × CNF ℕ => x.2.vars.all fun v => decide (v < NOf x.1))
      (encPair encP encCNF) encBool :=
    ComputableInPolyTime.allWithInput (by fun_prop) hlt
  unfold validDeclaredInput
  fun_prop

private theorem length_context_iterate_le {MOf : P → ℕ} {K k B D : ℕ} {p : P}
    (hM : 1 ≤ MOf p) (hK : 1 ≤ K) (hM2 : 2 ≤ MOf p) (hkK : k ≤ K)
    (hTB : CountingTreeBound (MOf p) K B D hM hK) (g : P × CNF ℕ → ℕ)
    (φ : CNF ℕ) (i : ℕ) :
    (encPair encP encState
      ((stepWith (fun q => countingThreshold (MOf q)) K g)^[i] (p, init k φ))).length ≤
      2 * (encP p).length + 1 + stateBound K D φ := by
  rw [iterate_stepWith_countingThreshold, length_encPair]
  exact Nat.add_le_add_left
    (iterate_step_prefix_bounds hM hK hM2 hkK hTB (fun ψ => g (p, ψ)) φ i).2.1 _

private theorem polyTime_inO {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} (hf : ComputableInPolyTime f encA encB) :
    ∃ d, ComputableInO f encA encB
      (fun x => ((encA x).length + 1) ^ d) (fun x => ((encA x).length + 1) ^ d) := by
  obtain ⟨d, _, h⟩ := hf.exists_degree
  exact ⟨d, h.inO⟩

private theorem computableInPolyTime_finish {NOf : P → ℕ}
    (hN : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × State => x.2.2.2 <<< (NOf x.1 - x.2.1))
      (encPair encP encState) encNat := by
  have hNu := hN.comp (ComputableInPolyTime.fst encP encState)
  have hmul : ComputableInPolyTime
      (fun x : P × State => x.2.2.2 * 2 ^ (NOf x.1 - x.2.1))
      (encPair encP encState) encNat := by
    unfold encState
    fun_prop
  simpa only [Nat.shiftLeft_eq] using hmul

/-- Normalize one total declared-count leaf implementation. The intermediate declared count is
charged explicitly in both resource bounds; semantic correctness still requires the support and
counting promises of `Cslib.Logic.PL.CNF.normalizeDeclaredLeaf_eq_modelCount`. -/
theorem exists_computableInO_normalizeDeclaredLeaf {NOf : P → ℕ}
    (hN : ComputableInPolyTime NOf encP encUnary)
    {h : P × CNF ℕ → ℕ} {t s : P × CNF ℕ → ℕ}
    (hh : ComputableInO h (encPair encP encCNF) encNat t s) :
    ∃ d, ComputableInO (normalizeDeclaredLeaf NOf h) (encPair encP encCNF) encNat
      (fun x => t x + ((encPair encP encCNF x).length + (encNat (h x)).length + 1) ^ d)
      (fun x => s x + ((encPair encP encCNF x).length + (encNat (h x)).length + 1) ^ d) := by
  have hNu : ComputableInPolyTime (fun x : (P × CNF ℕ) × ℕ => NOf x.1.1)
      (encPair (encPair encP encCNF) encNat) encUnary := by fun_prop
  have hpost : ComputableInPolyTime
      (fun x : (P × CNF ℕ) × ℕ => x.2 >>> (NOf x.1.1 - x.1.2.distinctVars.length))
      (encPair (encPair encP encCNF) encNat) encNat := by
    have hsub : ComputableInPolyTime
        (fun x : (P × CNF ℕ) × ℕ => NOf x.1.1 - x.1.2.distinctVars.length)
        (encPair (encPair encP encCNF) encNat) encUnary := by fun_prop
    exact ComputableInPolyTime.binary_shiftRight.comp
      ((ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.unary_to_binary.comp hsub))
  obtain ⟨d, hd⟩ := polyTime_inO hpost
  have hc := hd.comp ((ComputableInO.of_eq (f := id) (encIn := encPair encP encCNF)
    fun _ => rfl).prod hh)
  have hbound (v : P × CNF ℕ → ℕ) (x : P × CNF ℕ) :
      (encPair encP encCNF x).length + v x +
        ((encPair (encPair encP encCNF) encNat (x, h x)).length + 1) ^ d ≤
      (2 ^ d + 1) *
        (v x + ((encPair encP encCNF x).length + (encNat (h x)).length + 1) ^ (d + 1)) := by
    let W := (encPair encP encCNF x).length + (encNat (h x)).length + 1
    have hW : 1 ≤ W := by dsimp [W]; omega
    have hL : (encPair encP encCNF x).length ≤ W ^ (d + 1) :=
      (by dsimp [W]; omega : (encPair encP encCNF x).length ≤ W).trans
        (Nat.le_self_pow (by omega) W)
    have hp : ((encPair (encPair encP encCNF) encNat (x, h x)).length + 1) ^ d ≤
        2 ^ d * W ^ (d + 1) := by
      calc
        _ ≤ (2 * W) ^ d := Nat.pow_le_pow_left (by rw [length_encPair]; dsimp [W]; omega) d
        _ = 2 ^ d * W ^ d := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (by omega))
    have := Nat.zero_le (2 ^ d * v x)
    dsimp only [W] at hL hp
    nlinarith
  refine ⟨d + 1, (hc.mono (2 ^ d + 1)
    (fun x => (hbound t x).trans (Nat.mul_le_mul_left _ (by omega)))
    (fun x => (hbound s x).trans (Nat.mul_le_mul_left _ (by omega)))).of_enc_eq ?_⟩
  intro x
  rfl

private def stepCost (encP : P ↪ List Bool) (MOf : P → ℕ) (K d : ℕ)
    (g v : P × CNF ℕ → ℕ) (x : P × State) : ℕ :=
  ((encPair encP encState x).length + 1) ^ d +
    if x.2.2.1.isEmpty = false ∧
        isSparse (countingThreshold (MOf x.1)) K (x.2.2.1.headD []) = true then
      v (x.1, x.2.2.1.headD []) +
        ((encPair encP encState x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
    else 0

private theorem prefix_stepCost_le {MOf : P → ℕ} {K k B D : ℕ} {p : P}
    (hM : 1 ≤ MOf p) (hK : 1 ≤ K) (hM2 : 2 ≤ MOf p) (hkK : k ≤ K)
    (hTB : CountingTreeBound (MOf p) K B D hM hK) (g v : P × CNF ℕ → ℕ)
    (φ : CNF ℕ) (i d V : ℕ)
    (hg : let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k φ)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true →
      g (p, st.2.1.headD []) ≤ 2 ^ (st.2.1.headD []).numVars)
    (hv : let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k φ)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true →
      v (p, st.2.1.headD []) ≤ V) :
    stepCost encP MOf K d g v
      ((stepWith (fun q => countingThreshold (MOf q)) K g)^[i] (p, init k φ)) ≤
      2 * (2 * (2 * (encP p).length + 1 + stateBound K D φ) + 1) ^ d + V := by
  rw [iterate_stepWith_countingThreshold]
  let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k φ)
  let L := 2 * (encP p).length + 1 + stateBound K D φ
  have hprefix := iterate_step_prefix_bounds hM hK hM2 hkK hTB (fun ψ => g (p, ψ)) φ i
  have hstate : (encPair encP encState (p, st)).length ≤ L := by
    rw [length_encPair]
    exact Nat.add_le_add_left hprefix.2.1 _
  have hp₁ : ((encPair encP encState (p, st)).length + 1) ^ d ≤ (2 * L + 1) ^ d :=
    Nat.pow_le_pow_left (by omega) d
  change ((encPair encP encState (p, st)).length + 1) ^ d +
    (if st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true
      then v (p, st.2.1.headD []) +
        ((encPair encP encState (p, st)).length + (encNat (g (p, st.2.1.headD []))).length + 1) ^ d
      else 0) ≤ 2 * (2 * L + 1) ^ d + V
  split_ifs with hc
  · have hvars := (hprefix.2.2.2 hc).2.2.1
    have hglen : (encNat (g (p, st.2.1.headD []))).length ≤ φ.numVars + 1 :=
      length_encNat_le_of_le_two_pow ((hg hc).trans
        (Nat.pow_le_pow_right (by decide) hvars))
    have hnum : φ.numVars + 1 ≤ L := hprefix.2.2.1.trans (by dsimp [L]; omega)
    have hp₂ : ((encPair encP encState (p, st)).length +
        (encNat (g (p, st.2.1.headD []))).length + 1) ^ d ≤ (2 * L + 1) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    have hv' : v (p, st.2.1.headD []) ≤ V := hv hc
    omega
  · omega

private theorem declared_resources_of_step
    {NOf MOf BOf D : P → ℕ} {K k d : ℕ}
    (hN : ComputableInPolyTime NOf encP encUnary)
    (hB : ComputableInPolyTime BOf encP encNat)
    (hM : ∀ p, 1 ≤ MOf p) (hK : 1 ≤ K) (hM2 : ∀ p, 2 ≤ MOf p) (hkK : k ≤ K)
    (hTB : ∀ p, CountingTreeBound (MOf p) K (BOf p) (D p) (hM p) hK)
    (hD : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length) (fun x => D x.1))
    {g t s : P × CNF ℕ → ℕ} {R Q : P × CNF ℕ → ℕ}
    (hstep : ComputableInO (stepWith (fun p => countingThreshold (MOf p)) K g)
      (encPair encP encState) (encPair encP encState)
      (stepCost encP MOf K d g t) (stepCost encP MOf K d g s))
    (hg : ∀ x : P × CNF ℕ, validDeclaredInput k (NOf x.1) x.2 = true →
      ∀ i ≤ rounds (BOf x.1) x.2,
      let st := (step (MOf x.1) K (fun ψ => g (x.1, ψ)))^[i] (init k x.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf x.1)) K (st.2.1.headD []) = true →
      g (x.1, st.2.1.headD []) ≤ 2 ^ (st.2.1.headD []).numVars)
    (ht : ∀ x : P × CNF ℕ, validDeclaredInput k (NOf x.1) x.2 = true →
      ∀ i ≤ rounds (BOf x.1) x.2,
      let st := (step (MOf x.1) K (fun ψ => g (x.1, ψ)))^[i] (init k x.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf x.1)) K (st.2.1.headD []) = true →
      t (x.1, st.2.1.headD []) ≤ R x)
    (hs : ∀ x : P × CNF ℕ, validDeclaredInput k (NOf x.1) x.2 = true →
      ∀ i ≤ rounds (BOf x.1) x.2,
      let st := (step (MOf x.1) K (fun ψ => g (x.1, ψ)))^[i] (init k x.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf x.1)) K (st.2.1.headD []) = true →
      s (x.1, st.2.1.headD []) ≤ Q x)
    (hQ : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length) Q) :
    ∃ c e, ComputableInO
      (fun x : P × CNF ℕ => searchDeclaredWith NOf MOf BOf K k g x.1 x.2)
      (encPair encP encCNF) encNat
      (fun x => c * ((encPair encP encCNF x).length + 1) ^ e +
        (rounds (BOf x.1) x.2 + 1) * (c * ((encPair encP encCNF x).length + 1) ^ e + R x))
      (fun x => c * ((encPair encP encCNF x).length + 1) ^ e + Q x) ∧
      PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
        (fun x => c * ((encPair encP encCNF x).length + 1) ^ e + Q x) := by
  classical
  by_cases hp : Nonempty P
  swap
  · refine ⟨0, 0, ?_, ?_⟩
    · have hz : ComputableInO (fun _ : P × CNF ℕ => 0) (encPair encP encCNF) encNat
          (fun x => (rounds (BOf x.1) x.2 + 1) * R x) Q :=
        (ComputableInO.const (encIn := encPair encP encCNF) 0).mono_le
          (fun x => (hp ⟨x.1⟩).elim) (fun x => (hp ⟨x.1⟩).elim)
      simpa only [Nat.zero_mul, Nat.zero_add] using
        (hz.of_enc_eq (g := fun x => searchDeclaredWith NOf MOf BOf K k g x.1 x.2)
          fun x => (hp ⟨x.1⟩).elim)
    · simpa only [Nat.zero_mul, Nat.zero_add] using hQ
  let : Inhabited P := Classical.inhabited_of_nonempty hp
  let L (x : P × CNF ℕ) := (encPair encP encCNF x).length
  let q (x : P × CNF ℕ) := rounds (BOf x.1) x.2
  let B (x : P × CNF ℕ) := 2 * (encP x.1).length + 1 + stateBound K (D x.1) x.2
  let run (x : P × CNF ℕ) (i : ℕ) :=
    (stepWith (fun p => countingThreshold (MOf p)) K g)^[i] (x.1, init k x.2)
  let maxCost (v : P × CNF ℕ → ℕ) (x : P × CNF ℕ) :=
    (Finset.Iic (q x)).sup fun i => stepCost encP MOf K d g v (run x i)
  let A (x : P × CNF ℕ) := 2 * (2 * B x + 1) ^ d
  let clock (x : P × CNF ℕ) := (encNat (q x)).length
  have hstate (x : P × CNF ℕ) (i : ℕ) :
      (encPair encP encState (run x i)).length ≤ B x :=
    length_context_iterate_le (hM x.1) hK (hM2 x.1) hkK (hTB x.1) g x.2 i
  have hcost (v V : P × CNF ℕ → ℕ)
      (hv : ∀ x : P × CNF ℕ, validDeclaredInput k (NOf x.1) x.2 = true →
        ∀ i ≤ q x,
        let st := (step (MOf x.1) K (fun ψ => g (x.1, ψ)))^[i] (init k x.2)
        st.2.1.isEmpty = false ∧
          isSparse (countingThreshold (MOf x.1)) K (st.2.1.headD []) = true →
        v (x.1, st.2.1.headD []) ≤ V x)
      (x : P × CNF ℕ) (hx : validDeclaredInput k (NOf x.1) x.2 = true) :
      maxCost v x ≤ A x + V x := by
    apply Finset.sup_le
    intro i hi
    have hi' := Finset.mem_Iic.mp hi
    exact prefix_stepCost_le (hM x.1) hK (hM2 x.1) hkK (hTB x.1) g v x.2 i d (V x)
      (hg x hx i hi') (hv x hx i hi')
  obtain ⟨dn, hn⟩ := polyTime_inO (computableInPolyTime_roundsWith hB)
  obtain ⟨di, hi⟩ := polyTime_inO (computableInPolyTime_init_uniform (encP := encP) k)
  have hloop := ComputableInO.iterate hn hi hstep
    (R := maxCost t) (Q := maxCost s) (B := B)
    (fun x i hi => Finset.le_sup (f := fun j => stepCost encP MOf K d g t (run x j))
      (Finset.mem_Iic.mpr hi))
    (fun x i hi => Finset.le_sup (f := fun j => stepCost encP MOf K d g s (run x j))
      (Finset.mem_Iic.mpr hi))
    (fun x i _ => hstate x i)
  let I (x : P × CNF ℕ) := (L x + 1) ^ dn + (L x + 1) ^ di
  let Tloop (x : P × CNF ℕ) := I x + (q x + 1) * (maxCost t x + B x + (clock x + 1) ^ 2)
  let Sloop (x : P × CNF ℕ) := I x + maxCost s x + B x + clock x
  change ComputableInO (fun x => run x (q x)) (encPair encP encCNF) (encPair encP encState)
    Tloop Sloop at hloop
  obtain ⟨df, hf⟩ := polyTime_inO (computableInPolyTime_finish hN)
  let F (x : P × CNF ℕ) := (B x + 1) ^ df
  have hfinish (x : P × CNF ℕ) :
      ((encPair encP encState (run x (q x))).length + 1) ^ df ≤ F x :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hstate x (q x)) 1) df
  have hscaled := (hf.comp hloop).mono_le
    (fun x => Nat.add_le_add_left (hfinish x) (Tloop x))
    (fun x => Nat.add_le_add_left (hfinish x) (Sloop x))
  obtain ⟨dc, hc⟩ := polyTime_inO (computableInPolyTime_validDeclaredInput_uniform k hN)
  have hwhole := hc.ite hscaled (ComputableInO.const (encIn := encPair encP encCNF) 0)
  let W (x : P × CNF ℕ) := (L x + 1) ^ dc + I x + A x + B x +
    (clock x + 1) ^ 2 + clock x + F x + L x + 1
  have hW : PolyBounded L W := by
    have hL : PolyBounded L (fun x => L x + 1) := PolyBounded.self.add (.const 1)
    have hBs : PolyBounded L B := contextStateBound_polyBounded K hD
    have hclk : PolyBounded L clock := rounds_length_polyBounded BOf
    have hA := (PolyBounded.const 2).mul
      (PolyBounded.pow (((PolyBounded.const 2).mul hBs).add (.const 1)) d)
    exact ((((((((PolyBounded.pow hL dc).add
      ((PolyBounded.pow hL dn).add (PolyBounded.pow hL di))).add hA).add hBs).add
      (PolyBounded.pow (hclk.add (.const 1)) 2)).add hclk).add
      (PolyBounded.pow (hBs.add (.const 1)) df)).add PolyBounded.self).add (.const 1)
  have htime (x : P × CNF ℕ) :
      (L x + 1) ^ dc +
        (if validDeclaredInput k (NOf x.1) x.2 then Tloop x + F x else L x) ≤
      W x + (q x + 1) * (W x + R x) := by
    split_ifs with hx
    · have ht' := hcost t R ht x hx
      have hout : (L x + 1) ^ dc + I x + F x ≤ W x := by dsimp [W]; omega
      have hin : maxCost t x + B x + (clock x + 1) ^ 2 ≤ W x + R x := by
        dsimp only [W]
        omega
      calc
        _ = ((L x + 1) ^ dc + I x + F x) +
            (q x + 1) * (maxCost t x + B x + (clock x + 1) ^ 2) := by dsimp [Tloop]; ring
        _ ≤ _ := Nat.add_le_add hout (Nat.mul_le_mul_left _ hin)
    · have : (L x + 1) ^ dc + L x ≤ W x := by dsimp [W]; omega
      exact this.trans (Nat.le_add_right _ _)
  have hspace (x : P × CNF ℕ) :
      (L x + 1) ^ dc +
        (if validDeclaredInput k (NOf x.1) x.2 then Sloop x + F x else L x) ≤ W x + Q x := by
    split_ifs with hx
    · have hs' := hcost s Q hs x hx
      dsimp only [Sloop, W]
      omega
    · dsimp only [W]
      omega
  obtain ⟨c, e, hce⟩ := hW.exists_le
  refine ⟨c, e, ?_, ((PolyBounded.const c).mul
    (PolyBounded.pow (PolyBounded.self.add (.const 1)) e)).add hQ⟩
  have hcert := hwhole.mono_le
    (fun x => (htime x).trans (Nat.add_le_add (hce x)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hce x) (R x)))))
    (fun x => (hspace x).trans (Nat.add_le_add_right (hce x) (Q x)))
  refine hcert.of_enc_eq fun x => ?_
  have hret : (run x (q x)).2.1 = x.2.distinctVars.length := by
    dsimp only [run]
    rw [iterate_stepWith_countingThreshold]
    exact (iterate_step_prefix_bounds (hM x.1) hK (hM2 x.1) hkK (hTB x.1)
      (fun ψ => g (x.1, ψ)) x.2 (q x)).1
  simp only [searchDeclaredWith, Function.comp_apply]
  split_ifs
  · change encNat (searchWith MOf BOf K k g x.1 x.2 <<< (NOf x.1 - x.2.distinctVars.length)) =
      encNat ((run x (q x)).2.2.2 <<< (NOf (run x (q x)).1 - (run x (q x)).2.1))
    rw [hret]
    have hpar : (run x (q x)).1 = x.1 := iterate_stepWith_fst _ _ _ _ _
    rw [hpar]
    rfl
  · rfl

/-- The declared wrapper's binary output fits in `NOf p + 1` bits, even when the supplied leaf
routine is only a diagnostic. The old accumulator cap and the support guard suffice. -/
theorem length_encNat_searchDeclaredWith_le {NOf MOf BOf : P → ℕ} {K k D : ℕ} {p : P}
    (hM : 1 ≤ MOf p) (hK : 1 ≤ K) (hM2 : 2 ≤ MOf p) (hkK : k ≤ K)
    (hTB : CountingTreeBound (MOf p) K (BOf p) D hM hK)
    (g : P × CNF ℕ → ℕ) (φ : CNF ℕ) :
    (encNat (searchDeclaredWith NOf MOf BOf K k g p φ)).length ≤ NOf p + 1 := by
  rw [searchDeclaredWith_eq_ite_mul]
  split_ifs with hvalid
  · have hsub := (validDeclaredInput_eq_true_iff.mp hvalid).2
    have hn : φ.numVars ≤ NOf p := by
      simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsub
    obtain ⟨W, _, heq⟩ := (iterate_step hM hK hM2 hkK hTB (fun ψ => g (p, ψ)) φ).1
    have hcount : search (MOf p) K k (BOf p) (fun ψ => g (p, ψ)) φ ≤ 2 ^ φ.numVars := by
      unfold search
      rw [heq]
      simpa only [CNF.length_distinctVars] using Nat.min_le_left (2 ^ φ.distinctVars.length) _
    apply length_encNat_le_of_le_two_pow
    calc
      _ ≤ 2 ^ (NOf p - φ.numVars) * 2 ^ φ.numVars := Nat.mul_le_mul_left _ hcount
      _ = 2 ^ NOf p := by rw [← pow_add, Nat.sub_add_cancel hn]
  · change 0 ≤ NOf p + 1
    omega

private theorem declared_resources_input {C : Type} {encC : C ↪ List Bool}
    {MOf BOf : C × ℕ → ℕ} {K k c e : ℕ}
    {g R Q : (C × ℕ) × CNF ℕ → ℕ}
    (hcore : ComputableInO
      (fun x : (C × ℕ) × CNF ℕ => searchDeclaredWith Prod.snd MOf BOf K k g x.1 x.2)
      (encPair (encPair encC encUnary) encCNF) encNat
      (fun x => c * ((encPair (encPair encC encUnary) encCNF x).length + 1) ^ e +
        (rounds (BOf x.1) x.2 + 1) *
          (c * ((encPair (encPair encC encUnary) encCNF x).length + 1) ^ e + R x))
      (fun x => c * ((encPair (encPair encC encUnary) encCNF x).length + 1) ^ e + Q x))
    (hQ : PolyBounded (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
      (fun x => Q ((x.1, x.2.1), x.2.2))) :
    ∃ a d, ComputableInO
      (fun x : C × ℕ × CNF ℕ =>
        searchDeclaredWith Prod.snd MOf BOf K k g (x.1, x.2.1) x.2.2)
      (encPair encC (encPair encUnary encCNF)) encNat
      (fun x => a * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ d +
        (rounds (BOf (x.1, x.2.1)) x.2.2 + 1) *
          (a * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ d +
            R ((x.1, x.2.1), x.2.2)))
      (fun x => a * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ d +
        Q ((x.1, x.2.1), x.2.2)) ∧
      PolyBounded (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
        (fun x => a * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ d +
          Q ((x.1, x.2.1), x.2.2)) := by
  let rearrange (x : C × ℕ × CNF ℕ) := ((x.1, x.2.1), x.2.2)
  let L (x : C × ℕ × CNF ℕ) := (encPair encC (encPair encUnary encCNF) x).length
  let L' (x : C × ℕ × CNF ℕ) := (encPair (encPair encC encUnary) encCNF (rearrange x)).length
  have hp : ComputableInPolyTime rearrange (encPair encC (encPair encUnary encCNF))
      (encPair (encPair encC encUnary) encCNF) := by unfold rearrange; fun_prop
  obtain ⟨da, ha⟩ := polyTime_inO hp
  have hlen (x : C × ℕ × CNF ℕ) : L' x + 1 ≤ 2 * (L x + 1) := by
    dsimp only [L, L', rearrange]
    simp only [length_encPair]
    omega
  have hpoly (x : C × ℕ × CNF ℕ) :
      (L x + 1) ^ da + c * (L' x + 1) ^ e ≤
        (1 + c * 2 ^ e) * (L x + 1) ^ (da + e) := by
    have ha' := Nat.pow_le_pow_right (by omega : 1 ≤ L x + 1) (Nat.le_add_right da e)
    have he' := Nat.pow_le_pow_right (by omega : 1 ≤ L x + 1) (Nat.le_add_left e da)
    have hL' : (L' x + 1) ^ e ≤ 2 ^ e * (L x + 1) ^ (da + e) := by
      calc
        _ ≤ (2 * (L x + 1)) ^ e := Nat.pow_le_pow_left (hlen x) e
        _ = 2 ^ e * (L x + 1) ^ e := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _ he'
    nlinarith [Nat.mul_le_mul_left c hL']
  refine ⟨1 + c * 2 ^ e, da + e, ?_,
    ((PolyBounded.const _).mul (PolyBounded.pow (PolyBounded.self.add (.const 1)) _)).add hQ⟩
  refine ((hcore.comp ha).mono_le (fun x => ?_) (fun x => ?_)).of_enc_eq fun _ => rfl
  · have hinside : c * (L' x + 1) ^ e ≤ (1 + c * 2 ^ e) * (L x + 1) ^ (da + e) :=
      (Nat.le_add_left _ _).trans (hpoly x)
    have hsum := Nat.add_le_add (hpoly x)
      (Nat.mul_le_mul_left (rounds (BOf (x.1, x.2.1)) x.2.2 + 1)
        (Nat.add_le_add_right hinside (R (rearrange x))))
    dsimp only [Function.comp_apply, rearrange, L, L'] at hsum ⊢
    omega
  · have hsum := Nat.add_le_add_right (hpoly x) (Q (rearrange x))
    dsimp only [Function.comp_apply, rearrange, L, L'] at hsum ⊢
    omega

/-- Independent resources for the existing declared-variable search on one full runtime input.
The threshold-comparison and leaf certificates precede every input `(context, N, formula)`;
`N` is encoded in unary. The numerical depth and leaf-workspace envelopes are polynomial in
that complete encoded input, and the leaf promises concern every active prefix `i ≤ rounds`,
including the terminal prefix. The original occurring-support state and cap are unchanged.

The time bound contains the round count times a per-step allowance. The workspace bound contains
the independent leaf-workspace allowance and a polynomial for initialization, retained context,
all prefix states, binary clock, leaf output and final declared-variable scaling. It has
no factor of the number of rounds or the leaf time. Any prior preparation of a larger context must
be composed separately and charged against its own original external input. -/
theorem exists_computableInO_searchDeclaredWith {C : Type} {encC : C ↪ List Bool}
    {MOf BOf D : C × ℕ → ℕ} {K k : ℕ}
    (hB : ComputableInPolyTime BOf (encPair encC encUnary) encNat)
    (hθ : ComputableInPolyTime
      (fun x : (C × ℕ) × ℕ × ℕ => decide (countingThreshold (MOf x.1) x.2.1 ≤ x.2.2))
      (encPair (encPair encC encUnary) (encPair encUnary encUnary)) encBool)
    (hM : ∀ p, 1 ≤ MOf p) (hK : 1 ≤ K) (hM2 : ∀ p, 2 ≤ MOf p) (hkK : k ≤ K)
    (hTB : ∀ p, CountingTreeBound (MOf p) K (BOf p) (D p) (hM p) hK)
    (hD : PolyBounded
      (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
      (fun x => D (x.1, x.2.1)))
    {g t s : (C × ℕ) × CNF ℕ → ℕ} {R Q : C × ℕ × CNF ℕ → ℕ}
    (hcounter : ComputableInO g (encPair (encPair encC encUnary) encCNF) encNat t s)
    (hg : ∀ x : C × ℕ × CNF ℕ, validDeclaredInput k x.2.1 x.2.2 = true →
      ∀ i ≤ rounds (BOf (x.1, x.2.1)) x.2.2,
      let p := (x.1, x.2.1)
      let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true →
      g (p, st.2.1.headD []) ≤ 2 ^ (st.2.1.headD []).numVars)
    (ht : ∀ x : C × ℕ × CNF ℕ, validDeclaredInput k x.2.1 x.2.2 = true →
      ∀ i ≤ rounds (BOf (x.1, x.2.1)) x.2.2,
      let p := (x.1, x.2.1)
      let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true →
      t (p, st.2.1.headD []) ≤ R x)
    (hs : ∀ x : C × ℕ × CNF ℕ, validDeclaredInput k x.2.1 x.2.2 = true →
      ∀ i ≤ rounds (BOf (x.1, x.2.1)) x.2.2,
      let p := (x.1, x.2.1)
      let st := (step (MOf p) K (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (MOf p)) K (st.2.1.headD []) = true →
      s (p, st.2.1.headD []) ≤ Q x)
    (hQ : PolyBounded
      (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length) Q) :
    ∃ c e, ComputableInO
      (fun x : C × ℕ × CNF ℕ =>
        searchDeclaredWith Prod.snd MOf BOf K k g (x.1, x.2.1) x.2.2)
      (encPair encC (encPair encUnary encCNF)) encNat
      (fun x => c * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ e +
        (rounds (BOf (x.1, x.2.1)) x.2.2 + 1) *
          (c * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ e + R x))
      (fun x => c * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ e + Q x) ∧
      PolyBounded
        (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
        (fun x => c * ((encPair encC (encPair encUnary encCNF) x).length + 1) ^ e + Q x) := by
  let toFull (x : (C × ℕ) × CNF ℕ) := (x.1.1, x.1.2, x.2)
  have hfull : ComputableInPolyTime toFull (encPair (encPair encC encUnary) encCNF)
      (encPair encC (encPair encUnary encCNF)) := by unfold toFull; fun_prop
  have hD' := hD.comp hfull.polyBounded_length
  have hQ' := hQ.comp hfull.polyBounded_length
  obtain ⟨d, hstep⟩ := exists_computableInO_stepWith
    (θ := fun p => countingThreshold (MOf p)) hθ K hcounter
  change ComputableInO (stepWith (fun p => countingThreshold (MOf p)) K g)
    (encPair (encPair encC encUnary) encState) (encPair (encPair encC encUnary) encState)
    (stepCost (encPair encC encUnary) MOf K d g t)
    (stepCost (encPair encC encUnary) MOf K d g s) at hstep
  obtain ⟨c, e, hcore, _⟩ := declared_resources_of_step
    (show ComputableInPolyTime (Prod.snd : C × ℕ → ℕ) (encPair encC encUnary) encUnary by
      fun_prop)
    hB hM hK hM2 hkK hTB hD' hstep
    (fun x hx i hi => hg (toFull x) hx i hi)
    (fun x hx i hi => ht (toFull x) hx i hi)
    (fun x hx i hi => hs (toFull x) hx i hi) hQ'
  exact declared_resources_input hcore hQ

end Cslib.Complexity.CountingSparsify
