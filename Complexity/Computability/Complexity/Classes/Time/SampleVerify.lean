/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import Complexity.Probability.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PairSampler
import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Probability.PMF.Bind

/-!
# Sampling a random string and running a verifier, within explicit time

A fair-coin machine can draw a uniformly random string `w` of length `ℓ a` and output the verdict
`V (a, w)` of a deterministic verifier on the pair `(a, w)`, within the time it takes to write
`ℓ a` in unary and to run the verifier, up to constant factors
(`Cslib.Complexity.exists_machine_sampleVerify`). The machine is a closed fair-coin composition:

* a deterministic machine writes `frame (enc a)` followed by `ℓ a` ones;
* the fixed sampler `Turing.MultiTapePTM.pairSampler` copies the framed instance and replaces the
  ones by fair coins;
* a deterministic machine runs the verifier.

Every run halts within the clock, and the output is distributed as `[V (a, w)]` for `w` uniform of
length `ℓ a`. Read nondeterministically, the machine guesses and verifies a certificate
(`Cslib.Complexity.setOf_exists_mem_NTIME`); read probabilistically, it samples and verifies
(`Cslib.Complexity.mem_PromiseBPTIME_of_verifier`). Unlike the polynomial compiler of PPT
programs (`Cslib.Probability.IsPPTOn.exists_halting_machine`), the clock keeps the time bound up to
constant factors.

## Main results

* `Cslib.Complexity.exists_machine_sampleVerify`: the sample-and-verify machine within explicit
  time, with its output distribution.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Sample and verify, within explicit time.** If a verifier `V` is computable within time
`T (a, w)` on encoded pairs, and the length `ℓ a` of the random string is computable in unary
within time `Tℓ a`, and `(enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C` for every
string `w` of length `ℓ a`, then a fair-coin machine with a binary alphabet and finitely many
states halts on every run within time `c₁ * t (enc a).length + c₂` and outputs `[V (a, w)]` for a
uniformly random `w` of length `ℓ a`. -/
theorem exists_machine_sampleVerify {V : α × List Bool → Bool} {ℓ : α → ℕ} {t : ℕ → ℕ}
    {Tℓ Sℓ : α → ℕ} {T S : α × List Bool → ℕ} {C : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hV : ComputableInO V (encPair enc encBits) encBool T S)
    (ht : ∀ a w, w.length = ℓ a → (enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C) :
    ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
      ∀ a, (∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (c₁ * t (enc a).length + c₂)
          (machine.initialConfig (enc a)))).support, final.tapes.state = none) ∧
        ProbComp.eval (machine.runClosed (c₁ * t (enc a).length + c₂) (enc a)) =
          (BitString.uniformList (ℓ a)).map fun w => [V (a, w)] := by
  -- the deterministic preparation and the verifier, as machines
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, -⟩ :=
    (ComputableInO.of_eq (f := fun a : α => a) (encIn := enc) (encMid := enc) fun _ => rfl).prod hℓ
  obtain ⟨c₃, ⟨k₃, Q₃, _, tm₃, h₃⟩, -⟩ := hV
  let L (a : α) : ℕ := ℓ a
  let u (a : α) : List Bool := frame (enc a) ++ List.replicate (L a) true
  let t₁ (a : α) : ℕ := c₁ * ((enc a).length + Tℓ a + 1)
  let t₂ (a : α) : ℕ := (u a).length + 1
  let t₃ (a : α) : ℕ := c₃ * (C * t (enc a).length + C + 1)
  have hrun₁ (a : α) := (h₁ a).runFrom_of_le (le_refl (t₁ a))
  have hlen₁ (a : α) : (u a).length ≤ t₁ a := (h₁ a).length_output_le
  -- the first phase writes the framed instance and the unary length of the random string
  let M₁ : MultiTapePTM k₁ Bool Q₁ := MultiTapePTM.ofDeterministic tm₁
  have hfirst₁ (a : α) : ∀ final ∈ (ProbComp.eval
      (M₁.runClosedConfigFrom (t₁ a) (M₁.initialConfig (enc a)))).support,
      final.tapes.state = none := by
    intro final hfinal
    rw [MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal
    subst hfinal
    exact (hrun₁ a).1
  have hout₁ (a : α) : ProbComp.eval (M₁.runClosed (t₁ a) (enc a)) = PMF.pure (u a) := by
    rw [MultiTapePTM.eval_runClosed_ofDeterministic, (hrun₁ a).2]
    rfl
  -- the sampler copies the framed instance and draws the random string
  have hsecond₁ (a : α) : ∀ word ∈ (ProbComp.eval (M₁.runClosed (t₁ a) (enc a))).support,
      ∀ final ∈ (ProbComp.eval (MultiTapePTM.pairSampler.runClosedConfigFrom (t₂ a)
        (MultiTapePTM.pairSampler.initialConfig word))).support, final.tapes.state = none := by
    intro word hword
    rw [hout₁ a, PMF.mem_support_pure_iff] at hword
    subst hword
    exact MultiTapePTM.pairSampler_halted (enc a) (List.replicate (L a) true)
  let P₁₂ := MultiTapePTM.pairSampler.comp M₁ false
  let t₁₂ (a : α) : ℕ := t₁ a + (t₁ a + 4 + t₂ a)
  have heval₁₂ (a : α) : ProbComp.eval (P₁₂.runClosed (t₁₂ a) (enc a)) =
      (BitString.uniformList (L a)).map (frame (enc a) ++ ·) := by
    rw [MultiTapePTM.eval_comp M₁ MultiTapePTM.pairSampler false (enc a) (t₁ a) (t₂ a)
      (hfirst₁ a) (hsecond₁ a), hout₁ a, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    simpa only [List.length_replicate, u] using
      MultiTapePTM.eval_pairSampler (enc a) (List.replicate (L a) true)
  have hhalt₁₂ (a : α) := MultiTapePTM.comp_halted M₁ MultiTapePTM.pairSampler false (enc a)
    (t₁ a) (t₂ a) (hfirst₁ a) (hsecond₁ a)
  -- the verifier runs on every sampled pair within the uniform clock `t₃`
  let M₃ : MultiTapePTM k₃ Bool Q₃ := MultiTapePTM.ofDeterministic tm₃
  have hrun₃ (a : α) (w : List Bool) (hw : w.length = L a) :=
    (h₃ (a, w)).runFrom_of_le (J := t₃ a) (Nat.mul_le_mul_left c₃ (by
      have := ht a w hw
      omega))
  have hword (a : α) {word : List Bool}
      (hword : word ∈ (ProbComp.eval (P₁₂.runClosed (t₁₂ a) (enc a))).support) :
      ∃ w : List Bool, w.length = L a ∧ word = encPair enc encBits (a, w) := by
    rw [heval₁₂ a] at hword
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
    exact ⟨w, BitString.mem_support_uniformList_iff.mp hw, rfl⟩
  have hsecond₂ (a : α) : ∀ word ∈ (ProbComp.eval (P₁₂.runClosed (t₁₂ a) (enc a))).support,
      ∀ final ∈ (ProbComp.eval (M₃.runClosedConfigFrom (t₃ a) (M₃.initialConfig word))).support,
      final.tapes.state = none := by
    intro word hw final hfinal
    obtain ⟨w, hwlen, rfl⟩ := hword a hw
    rw [MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal
    subst hfinal
    exact (hrun₃ a w hwlen).1
  let P := M₃.comp P₁₂ false
  let total (a : α) : ℕ := t₁₂ a + (t₁₂ a + 4 + t₃ a)
  have hhalt (a : α) := MultiTapePTM.comp_halted P₁₂ M₃ false (enc a) (t₁₂ a) (t₃ a) (hhalt₁₂ a)
    (hsecond₂ a)
  -- the output is the verdict on a uniformly random string
  have heval (a : α) : ProbComp.eval (P.runClosed (total a) (enc a)) =
      (BitString.uniformList (ℓ a)).map fun w => [V (a, w)] := by
    rw [MultiTapePTM.eval_comp P₁₂ M₃ false (enc a) (t₁₂ a) (t₃ a) (hhalt₁₂ a) (hsecond₂ a),
      Probability.PMF.monad_bind_eq_bind, heval₁₂ a, PMF.bind_map, ← PMF.bind_pure_comp]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun w hw => ?_
    have hwlen : w.length = L a := BitString.mem_support_uniformList_iff.mp hw
    simp only [Function.comp_apply]
    rw [MultiTapePTM.eval_runClosed_ofDeterministic]
    exact congrArg PMF.pure (hrun₃ a w hwlen).2
  -- the composed clock is within `O(t)`
  have hle (a : α) : total a ≤ (6 * c₁ + c₃) * C * t (enc a).length +
      ((6 * c₁ + c₃) * (C + 1) + 14) := by
    set X := C * t (enc a).length + C + 1
    have hX₁ : t₁ a ≤ c₁ * X := Nat.mul_le_mul_left c₁ (by
      have := ht a (List.replicate (L a) false) (List.length_replicate ..)
      omega)
    have htotal : total a ≤ 6 * t₁ a + 14 + t₃ a := by
      have := hlen₁ a
      simp only [total, t₁₂, t₂]
      omega
    have hX₃ : t₃ a = c₃ * X := rfl
    calc total a ≤ 6 * (c₁ * X) + 14 + c₃ * X := by
          have := Nat.mul_le_mul_left 6 hX₁
          rw [hX₃] at htotal
          omega
      _ = (6 * c₁ + c₃) * C * t (enc a).length + ((6 * c₁ + c₃) * (C + 1) + 14) := by
          simp only [X]
          ring
  refine ⟨(6 * c₁ + c₃) * C, (6 * c₁ + c₃) * (C + 1) + 14, _, _, inferInstance, P, fun a => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [P.eval_runClosedConfigFrom_eq_of_halted _ (hle a) (hhalt a)]
    exact hhalt a
  · rw [P.eval_runClosed_eq_of_halted _ (hle a) (hhalt a)]
    exact heval a

end Cslib.Complexity
