/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FPAUS.Counting
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Almost uniform samplers give FPRAS for self-reducible families

The sampling-to-counting estimator of `Cslib.Complexity.SelfReducible.estimate` is a strict
probabilistic polynomial-time program whenever the sampler is, so for a self-reducible witness
family a fully polynomial almost uniform sampler yields a fully polynomial randomized
approximation scheme for the number of witnesses
[Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2.1][Sinclair2025].

The estimator runs `len x` levels. Each level calls the sampler `2 N` times on the current
instance, which is no longer than `x`, with accuracy `M` in unary, where `M` and `N` are
polynomial in `len x`, `p` and `t`. Its state is the current instance with a numerator and
denominator in binary, each at most `N ^ i` after `i` levels, so every reachable state has
encoded length polynomial in that of `(x, p, t)`
(`Cslib.Probability.IsPPTOn.iterateWith_spec'`).

## Main results

* `Cslib.Complexity.SelfReducible.isPPTOn_estimate`: the estimator is strict PPT.
* `Cslib.Complexity.SelfReducible.isFPRAS_of_isFPAUS`: **an FPAUS gives an FPRAS**.
* `Cslib.Complexity.SelfReducible.mem_FPRAS_of_mem_FPAUS`: the class form.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.1][Sinclair2025]
-/

public section

namespace Cslib.Complexity.SelfReducible

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}
  (R : SelfReducible enc W)

/-- The estimator input `(x, p, t)`, with `p` and `t` in unary. -/
private abbrev encInput (enc : α ↪ List Bool) : α × ℕ × ℕ ↪ List Bool :=
  encPair enc (encPair encUnary encUnary)

/-- The estimator state: the current instance, with numerator and denominator in binary. -/
private abbrev encState (enc : α ↪ List Bool) : State α ↪ List Bool :=
  encPair enc (encPair encNat encNat)

/-! ### Deterministic parts -/

private theorem computableInPolyTime_len_fst {β : Type} {encB : β ↪ List Bool} :
    ComputableInPolyTime (fun a : α × β => R.len a.1) (encPair enc encB) encUnary :=
  R.len_polytime.comp (ComputableInPolyTime.fst _ _)

private theorem computableInPolyTime_tolerance :
    ComputableInPolyTime (fun a : α × ℕ × ℕ => tolerance (R.len a.1) a.2.1) (encInput enc)
      encUnary := by
  have h := R.computableInPolyTime_len_fst (encB := encPair encUnary encUnary)
  unfold tolerance
  fun_prop

private theorem computableInPolyTime_sampleCount :
    ComputableInPolyTime (fun a : α × ℕ × ℕ => sampleCount (R.len a.1) a.2.1 a.2.2)
      (encInput enc) encUnary := by
  have h := R.computableInPolyTime_len_fst (encB := encPair encUnary encUnary)
  unfold sampleCount tolerance
  fun_prop

private theorem computableInPolyTime_startsWith (b : Bool) :
    ComputableInPolyTime (startsWith b) (encOption encBits) encBool := by
  cases b <;> unfold startsWith <;> fun_prop

private theorem child_comp {β : Type} {encB : β ↪ List Bool} {f : β → α} {g : β → Bool}
    (hf : ComputableInPolyTime f encB enc) (hg : ComputableInPolyTime g encB encBool) :
    ComputableInPolyTime (fun b => R.child (f b) (g b)) encB enc :=
  R.child_polytime.comp (hf.prod hg)

private theorem sampleCount_pos (ℓ p t : ℕ) : 0 < sampleCount ℓ p t := by
  unfold sampleCount tolerance
  positivity

/-! ### Probabilistic polynomial time -/

variable {S : α → ℕ → ProbComp (Option (List Bool))}

/-- The sampler call of one level, on the captured input and the current state. -/
private theorem isPPTOn_sample
    (hS : IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S)) (b : Bool) :
    IsPPTOn (encPair (encInput enc) (encState enc)) encBool
      (fun r : (α × ℕ × ℕ) × State α =>
        startsWith b <$> S r.2.1 (tolerance (R.len r.1.1) r.1.2.1)) := by
  have htol := R.computableInPolyTime_tolerance.comp
    (ComputableInPolyTime.fst (encInput enc) (encState enc))
  have hprep : ComputableInPolyTime
      (fun r : (α × ℕ × ℕ) × State α => (r.2.1, tolerance (R.len r.1.1) r.1.2.1))
      (encPair (encInput enc) (encState enc)) (encPair enc encUnary) := by
    simp only [Function.comp_def] at htol
    fun_prop
  exact (hS.preprocess hprep).map (computableInPolyTime_startsWith b)

/-- One level of the estimator is strict PPT on the captured input and the current state. -/
private theorem isPPTOn_step
    (hS : IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S)) :
    IsPPTOn (encPair (encInput enc) (encState enc)) (encState enc)
      (fun r : (α × ℕ × ℕ) × State α =>
        R.step S (R.len r.1.1) r.1.2.1 r.1.2.2 r.2) := by
  have hN := R.computableInPolyTime_sampleCount.comp
    (ComputableInPolyTime.fst (encInput enc) (encState enc))
  simp only [Function.comp_def] at hN
  have h₀ := IsPPTOn.countTrue (R.isPPTOn_sample hS false) hN
  have h₁ := IsPPTOn.countTrue (R.isPPTOn_sample hS true) hN
  have hlt : ComputableInPolyTime
      (fun u : (((α × ℕ × ℕ) × State α) × ℕ) × ℕ => decide (u.1.2 < u.2))
      (encPair (encPair (encPair (encInput enc) (encState enc)) encUnary) encUnary) encBool := by
    fun_prop
  have hfst : ComputableInPolyTime (fun u : (((α × ℕ × ℕ) × State α) × ℕ) × ℕ => u.1.1.2.1)
      (encPair (encPair (encPair (encInput enc) (encState enc)) encUnary) encUnary) enc := by
    fun_prop
  have hN' := hN.comp (ComputableInPolyTime.fst (encPair (encInput enc) (encState enc)) encUnary)
  have hN'' := hN'.comp
    (ComputableInPolyTime.fst (encPair (encPair (encInput enc) (encState enc)) encUnary) encUnary)
  simp only [Function.comp_def] at hN''
  have hnext : ComputableInPolyTime
      (fun u : (((α × ℕ × ℕ) × State α) × ℕ) × ℕ =>
        R.next (sampleCount (R.len u.1.1.1.1) u.1.1.1.2.1 u.1.1.1.2.2) u.1.1.2 u.1.2 u.2)
      (encPair (encPair (encPair (encInput enc) (encState enc)) encUnary) encUnary)
      (encState enc) := by
    unfold next
    have hchild := R.child_comp hfst hlt
    fun_prop
  have hsecond : IsPPTOn (encPair (encPair (encInput enc) (encState enc)) encUnary) (encState enc)
      (fun v : ((α × ℕ × ℕ) × State α) × ℕ =>
        R.next (sampleCount (R.len v.1.1.1) v.1.1.2.1 v.1.1.2.2) v.1.2 v.2 <$>
          OracleComp.countTrue (sampleCount (R.len v.1.1.1) v.1.1.2.1 v.1.1.2.2)
            (startsWith true <$> S v.1.2.1 (tolerance (R.len v.1.1.1) v.1.1.2.1))) :=
    IsPPTOn.map_with
      (h₁.preprocess (ComputableInPolyTime.fst (encPair (encInput enc) (encState enc)) encUnary))
      hnext
  exact IsPPTOn.bind_with h₀ hsecond

/-- **The sampling-to-counting estimator is strict PPT** on the instance and the unary parameters
`p` and `t`, with the estimate written in binary. The state invariant: after `i` levels the
current instance is no longer than `x`, and the numerator and denominator are at most `N ^ i`. -/
theorem isPPTOn_estimate
    (hS : IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S)) :
    IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (R.estimate S x)) := by
  set N : α × ℕ × ℕ → ℕ := fun a => sampleCount (R.len a.1) a.2.1 a.2.2 with hN_def
  have hcount : ComputableInPolyTime (fun a : α × ℕ × ℕ => R.len a.1) (encInput enc) encUnary :=
    R.computableInPolyTime_len_fst
  have hinitial : ComputableInPolyTime (fun a : α × ℕ × ℕ => ((a.1, 1, 1) : State α))
      (encInput enc) (encState enc) := by
    fun_prop
  have hNc := R.computableInPolyTime_sampleCount
  have hpowc : ComputableInPolyTime (fun a : α × ℕ × ℕ => N a ^ R.len a.1) (encInput enc)
      encNat := by
    simp only [hN_def]
    fun_prop
  have hsize : PolyBounded (fun a => (encInput enc a).length)
      (fun a => 3 * (encInput enc a).length + 4 * (encNat (N a ^ R.len a.1)).length + 2) := by
    growth_poly
  have hloop := IsPPTOn.iterateWith_spec' (input := encInput enc) (stateEncoding := encState enc)
    (step := fun a => R.step S (R.len a.1) a.2.1 a.2.2) hcount hinitial (R.isPPTOn_step hS)
    (fun a i s => R.len s.1 + i = R.len a.1 ∧ (enc s.1).length ≤ (enc a.1).length ∧
      s.2.1 ≤ N a ^ i ∧ s.2.2 ≤ N a ^ i)
    (fun a => ⟨by simp, le_rfl, by simp, by simp⟩)
    (fun a i s hi ⟨hlen, henc, hnum, hden⟩ s' hs' => by
      obtain ⟨c₀, c₁, hc₀, hc₁, rfl⟩ := R.mem_support_step hs'
      have hpos : 0 < R.len s.1 := by omega
      have hNpos : 0 < N a := sampleCount_pos _ _ _
      refine ⟨?_, (R.length_child_le s.1 hpos _).trans henc, ?_, ?_⟩
      · simp only [next]
        rw [R.len_child s.1 hpos]
        omega
      · simp only [next, pow_succ]
        exact Nat.mul_le_mul hnum le_rfl
      · simp only [next, pow_succ]
        exact Nat.mul_le_mul hden (max_le (max_le hc₀ hc₁) hNpos))
    hsize
    (fun a i s hi ⟨_, henc, hnum, hden⟩ => by
      have hNpos : 0 < N a := sampleCount_pos _ _ _
      have hmono : N a ^ i ≤ N a ^ R.len a.1 := Nat.pow_le_pow_right hNpos hi
      have h1 := length_encNat_mono (hnum.trans hmono)
      have h2 := length_encNat_mono (hden.trans hmono)
      have hx : (enc a.1).length ≤ (encInput enc a).length := by
        rw [length_encPair]
        omega
      rw [length_encPair, length_encPair]
      omega)
  have hpost : ComputableInPolyTime
      (fun s : State α => (if [] ∈ W s.1 then s.2.1 else 0, s.2.2))
      (encState enc) (encPair encNat encNat) := by
    have hnil := R.nil_mem_polytime.comp (ComputableInPolyTime.fst enc (encPair encNat encNat))
    simp only [Function.comp_def] at hnil
    have heq : (fun s : State α => (if [] ∈ W s.1 then s.2.1 else 0, s.2.2)) =
        fun s => (if decide ([] ∈ W s.1) = true then s.2.1 else 0, s.2.2) := by
      funext s
      simp only [decide_eq_true_eq]
    rw [heq]
    fun_prop
  exact hloop.1.map hpost

/-- **An almost uniform sampler gives an approximate counter**: for a self-reducible witness
family, a fully polynomial almost uniform sampler `S` yields a fully polynomial randomized
approximation scheme `R.estimate S` for the number of witnesses. -/
theorem isFPRAS_of_isFPAUS (hS : IsFPAUS enc W S) :
    IsFPRAS enc (fun x => (W x).card) (R.estimate S) :=
  ⟨R.isPPTOn_estimate hS.1, fun x _ t hp => R.approxWithin_estimate hS.2 x hp t⟩

include R in
/-- **The class form**: a self-reducible witness family with a fully polynomial almost uniform
sampler has a fully polynomial randomized approximation scheme for its witness counts. -/
theorem mem_FPRAS_of_mem_FPAUS (hW : W ∈ FPAUS enc) : (fun x => (W x).card) ∈ FPRAS enc :=
  let ⟨S, hS⟩ := hW
  ⟨R.estimate S, R.isFPRAS_of_isFPAUS hS⟩

end Cslib.Complexity.SelfReducible
