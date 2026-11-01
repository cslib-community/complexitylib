/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.NP.Nondeterministic
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PairSampler
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Probability.BitString
import Complexity.Probability.PMF.Bind

/-!
# Nondeterministic time through verifiers, with explicit bounds

This module characterizes `Cslib.Complexity.NTIME enc t` by deterministic verifiers, keeping the
time bound up to constant factors. The polynomial characterization of `NP`
(`Cslib.Complexity.mem_NP_iff_decidableInPolyTime`) loses the degree in both directions. The
two directions here keep it.

* **Guess and verify** (`Cslib.Complexity.setOf_exists_mem_NTIME`). Suppose a verifier `V` is
  computable within time `T (a, w)` on encoded pairs, and a certificate length `ℓ a` is
  computable in unary within time `Tℓ a`. Then the problem
  `{a | ∃ w, w.length = ℓ a ∧ V (a, w) = true}` lies in `NTIME enc t` whenever
  `(enc a).length + Tℓ a + T (a, w)` is within `O(t (enc a).length)` on certificates of that
  length. The certificate length may depend on the instance, not only on its encoded length.
  The machine is the nondeterministic reading of a closed fair-coin composition:
  - a deterministic machine writes `frame (enc a)` followed by `ℓ` ones;
  - the fixed sampler `Turing.MultiTapePTM.pairSampler` copies the framed instance and replaces
    the ones by fair coins;
  - a deterministic machine runs the verifier.

  Its computation paths are exactly the coin replays, so it accepts exactly when some
  certificate is accepted, and every branch halts within the composed clock.
* **Verifiers from nondeterministic time** (`Cslib.Complexity.exists_verifier_of_mem_NTIME`).
  A problem in `NTIME enc t` has a verifier that is computable in linear time on encoded pairs:
  check that the certificate, read as coins of the choice table
  (`Turing.MultiTapeNTM.checkChoices`), replays an accepting computation. Every certificate
  length of at least `c * t (enc a).length + c` works, for a constant `c`.

These are explicit-time forms of the guess-and-verify characterization of nondeterministic
polynomial time [Arora and Barak][AroraBarak09]: the choices of an accepting computation are a
certificate, and a certificate can be guessed and then checked.

## Main results

* `Cslib.Complexity.setOf_exists_mem_NTIME`: guess and verify within explicit time.
* `Cslib.Complexity.exists_verifier_of_mem_NTIME`: a linear-time verifier for a problem in
  `NTIME`, with certificates of every sufficient length.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Guess and verify, within explicit time.** If a verifier `V` is computable within time
`T (a, w)` on encoded pairs, and the certificate length `ℓ a` is computable in unary within time
`Tℓ a`, then the problem of instances with an accepted certificate of that length is in
`NTIME enc t`, provided `(enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C` for every
certificate `w` of that length. -/
theorem setOf_exists_mem_NTIME {V : α × List Bool → Bool} {ℓ : α → ℕ} {t : ℕ → ℕ}
    {Tℓ Sℓ : α → ℕ} {T S : α × List Bool → ℕ} {C : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hV : ComputableInO V (encPair enc encBits) encBool T S)
    (ht : ∀ a w, w.length = ℓ a → (enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C) :
    {a | ∃ w : List Bool, w.length = ℓ a ∧ V (a, w) = true} ∈ NTIME enc t := by
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
  -- the first phase writes the framed instance and the unary certificate length
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
  -- the sampler copies the framed instance and guesses the certificate
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
  -- the verifier runs on every guessed pair within the uniform clock `t₃`
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
  -- the nondeterministic reading decides the problem
  have hdec : P.toNTM.DecidesInTime enc
      {a | ∃ w : List Bool, w.length = ℓ a ∧ V (a, w) = true} total := by
    intro a
    have htime : P.toNTM.RunsInTime (enc a) (total a) := P.runsInTime_toNTM
      (MultiTapePTM.comp_halted P₁₂ M₃ false (enc a) (t₁₂ a) (t₃ a) (hhalt₁₂ a) (hsecond₂ a))
    refine ⟨htime, ?_⟩
    rw [MultiTapeNTM.accepts_iff_exists_time_eq htime,
      P.exists_computationPath_toNTM_iff (P := fun cfg => cfg.output = [true])]
    have hiff : (∃ final ∈ (ProbComp.eval (P.runClosedConfigFrom (total a)
        (P.initialConfig (enc a)))).support, final.tapes.output = [true]) ↔
        [true] ∈ (ProbComp.eval (P.runClosed (total a) (enc a))).support := by
      rw [MultiTapePTM.runClosed_eq_map, ProbComp.eval_map, PMF.mem_support_map_iff]
    rw [hiff, MultiTapePTM.eval_comp P₁₂ M₃ false (enc a) (t₁₂ a) (t₃ a) (hhalt₁₂ a)
      (hsecond₂ a), Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
    constructor
    · rintro ⟨w, hw, hV⟩
      refine ⟨encPair enc encBits (a, w), ?_, ?_⟩
      · rw [heval₁₂ a]
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨w, BitString.mem_support_uniformList_iff.mpr hw, rfl⟩
      · rw [MultiTapePTM.eval_runClosed_ofDeterministic, (hrun₃ a w hw).2, PMF.mem_support_pure_iff]
        simp [hV]
    · rintro ⟨word, hw, hacc⟩
      obtain ⟨w, hwlen, rfl⟩ := hword a hw
      rw [MultiTapePTM.eval_runClosed_ofDeterministic, (hrun₃ a w hwlen).2,
        PMF.mem_support_pure_iff] at hacc
      exact ⟨w, hwlen, by simpa using hacc⟩
  -- the composed clock is within `O(t)`
  refine ⟨(6 * c₁ + c₃) * C, (6 * c₁ + c₃) * (C + 1) + 14, _, _, inferInstance, P.toNTM,
    hdec.mono fun a => ?_⟩
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

/-- **A linear-time verifier for nondeterministic time.** A problem in `NTIME enc t` has a
verifier computable in linear time on encoded pairs. For a constant `c`, every certificate length
`L ≥ c * t (enc a).length + c` works: `a ∈ A` exactly when some certificate of length `L` is
accepted. The verifier checks that the certificate, read as coins of the choice table, replays an
accepting computation. -/
theorem exists_verifier_of_mem_NTIME {A : Set α} {t : ℕ → ℕ} (hA : A ∈ NTIME enc t) :
    ∃ (V : α × List Bool → Bool) (c : ℕ),
      ComputableInO V (encPair enc encBits) encBool (fun p => (encPair enc encBits p).length)
        (fun p => (encPair enc encBits p).length) ∧
      ∀ a L, c * t (enc a).length + c ≤ L →
        (a ∈ A ↔ ∃ w : List Bool, w.length = L ∧ V (a, w) = true) := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hA
  set M := Nat.card (Turing.Action k Bool State)
  refine ⟨ntm.checkChoices enc, M * (c₁ + c₂), ?_, fun a L hL =>
    hdec.mem_iff_exists_checkChoices ?_⟩
  · -- replay the certificate with the choice table, then compare the output with `[true]`
    have hswap : ComputableInO (fun p : α × List Bool => (p.2, enc p.1)) (encPair enc encBits)
        (encPair encBits encBits)
        (fun p => (encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length))
        (fun p => (encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length)) :=
      (ComputableInO.snd enc encBits).prod
        ((ComputableInO.of_eq (f := fun x : α => enc x) (encIn := enc) (encMid := encBits)
          fun _ => rfl).comp (ComputableInO.fst enc encBits))
    have hrun := (ComputableInO.of_linear
      (MultiTapePTM.computableInLinearTimeAndSpace_runClosedCoins ntm.choiceTable)).comp hswap
    obtain ⟨cr, hcr⟩ := hrun.length_le_time
    have heq := ComputableInO.eqWords.comp ((ComputableInO.const (encIn := encPair enc encBits)
      (encMid := encBits) [true]).prod hrun)
    have hfun : ((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
        fun p : α × List Bool => ([true], ((fun q : List Bool × List Bool =>
          ntm.choiceTable.runClosedCoins q.1 q.2) ∘ fun p : α × List Bool => (p.2, enc p.1)) p)) =
        ntm.checkChoices enc := by
      funext p
      simp [MultiTapeNTM.checkChoices, eq_comm]
    rw [hfun] at heq
    -- every part is linear in the encoded pair, including the replayed output
    have hbound (p : α × List Bool) :
        (encPair enc encBits p).length + ((encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length) +
          (encPair encBits encBits (p.2, enc p.1)).length) +
        2 * ((ntm.choiceTable.runClosedCoins p.2 (enc p.1)).length + 2) ≤
          (9 + 10 * cr) * ((encPair enc encBits p).length + 1) := by
      have hc := hcr p
      simp only [Function.comp_apply, encBits_apply] at hc
      have hle : (enc p.1).length ≤ (encPair enc encBits p).length := by
        simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
        omega
      have hsw : (encPair encBits encBits (p.2, enc p.1)).length ≤
          2 * (encPair enc encBits p).length := by
        simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
        omega
      generalize (encPair enc encBits p).length = N at *
      generalize (ntm.choiceTable.runClosedCoins p.2 (enc p.1)).length = R at *
      generalize (encPair encBits encBits (p.2, enc p.1)).length = W at *
      have hR : R ≤ cr * (5 * N + 1) := hc.trans (Nat.mul_le_mul_left cr (by omega))
      nlinarith
    refine heq.mono (9 + 10 * cr) (fun p => ?_) fun p => ?_
    · have := hbound p
      simp only [Function.comp_apply, List.length_singleton] at this ⊢
      nlinarith
    · have := hbound p
      simp only [Function.comp_apply, List.length_singleton] at this ⊢
      omega
  · have hmul : M * (c₁ * t (enc a).length + c₂) ≤
        M * (c₁ + c₂) * t (enc a).length + M * (c₁ + c₂) := by
      rw [Nat.mul_assoc, ← Nat.mul_add]
      exact Nat.mul_le_mul_left M (by nlinarith)
    exact hmul.trans hL

end Cslib.Complexity
