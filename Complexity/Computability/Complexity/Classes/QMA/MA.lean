/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin
public import Complexity.Computability.Complexity.Classes.QMA.NP
public import Complexity.Computability.Circuit.Quantum.HadamardLayer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# `MA ⊆ QMA` and `BPP ⊆ BQP`

A Merlin–Arthur verifier `V` (`Cslib.Complexity.MA`) reads Merlin's proof `y` of length `q(n)`
and Arthur's random string `r` of length `p(n)`. Its quantum simulation
(`Cslib.Quantum.UniformVerifierFamily.ofMA`) does the following:

* it reads Merlin's proof as a witness state on `q(n)` qubits;
* it prepares Arthur's coins with one Hadamard gate on each of `p(n)` fresh zero qubits
  (`Cslib.Quantum.hadamardCodes`);
* it runs the exact reversible simulation of `V` on the word `x ++ y ++ r` from `QMA/NP.lean`
  (`Cslib.Quantum.UniformVerifierFamily.ofNP`).

This is the gate-by-gate simulation of randomized circuits, with random bits produced by Hadamard
gates, of [Watrous][Watrous2008], Section IV.3 (Figure 7), there used for `BPP ⊆ BQP`; the
containment `MA ⊆ QMA` appears in the inclusion diagram of [Watrous][Watrous2008], Figure 14.

The classical part maps basis states to basis states, each accepted with probability `0` or `1`,
so different proofs and coin strings do not interfere. On a witness state `ψ = ∑_y ψ_y |y⟩`, the
verifier accepts with probability `∑_y |ψ_y|² · #{r | V(x, y ++ r)} / 2^{p(n)}`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb_ofMA`), the average over a distribution of
proofs of their classical acceptance probabilities. A basis state of a good proof gives
completeness, and soundness holds for every witness state, entangled or not, since an average of
values at most `1 / 3` is at most `1 / 3`. With no proof (`q = 0`), the same verifier is a `BQP`
family for a `BPP` verifier.

## Main definitions

* `Cslib.Quantum.UniformVerifierFamily.ofMA`: the quantum verifier of a Merlin–Arthur verifier.

## Main results

* `Cslib.Quantum.UniformVerifierFamily.acceptProb_ofMA`: its acceptance probability.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb_ofMA_ket`: on a basis proof, the classical
  acceptance probability.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb_ofMA_le`: soundness against every witness state.
* `Cslib.Complexity.MA_subset_QMA`: `MA ⊆ QMA`.
* `Cslib.Complexity.BPP_subset_BQP`: `BPP ⊆ BQP`.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

/-! ### The verifier of a Merlin–Arthur verifier -/

namespace MAVerifier

/-- The verifier's circuit: Hadamard gates on the `p(n)` qubits after Merlin's `q(n)`-qubit proof,
then the verifier of the NP relation on proofs of length `q(n) + p(n)`. -/
noncomputable def gates (F : UniformCircuitFamily) (q p : Polynomial ℕ) (n : ℕ) : List GateCode :=
  hadamardCodes (n + q.eval n) (p.eval n) ++ NPVerifier.gates F (q + p) n

end MAVerifier

namespace UniformVerifierFamily

open NPVerifier MAVerifier

/-- **The quantum verifier of a Merlin–Arthur verifier**: for a uniform family `F` of circuits on
the words `frame x ++ y ++ r`, the verifier reads Merlin's proof as a witness of `q(|x|)` qubits,
prepares Arthur's `p(|x|)` coins in uniform superposition with Hadamard gates, and runs the verifier
of the NP relation of `F` on proofs of length `q + p`. -/
noncomputable def ofMA (F : UniformCircuitFamily) (q p : Polynomial ℕ) : UniformVerifierFamily where
  width := NPVerifier.width F (q + p)
  gates := MAVerifier.gates F q p
  computableInPolyTime_width := (ofNP F (q + p)).computableInPolyTime_width
  computableInPolyTime_gates := by
    have hNP : ComputableInPolyTime (fun n => NPVerifier.gates F (q + p) n) encUnary
        (encList encGateCode) := (ofNP F (q + p)).computableInPolyTime_gates
    have hc := computableInPolyTime_hadamardCodes (enc := encUnary) (o := fun n => n + q.eval n)
      (p := fun n => p.eval n) (by fun_prop) (by fun_prop)
    change ComputableInPolyTime (fun n => hadamardCodes (n + q.eval n) (p.eval n) ++
      NPVerifier.gates F (q + p) n) encUnary (encList encGateCode)
    fun_prop
  le_width := (ofNP F (q + p)).le_width
  width_pos := (ofNP F (q + p)).width_pos
  wellFormed n g hg := by
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      refine ⟨?_, rfl⟩
      rw [List.mem_range] at hj
      have := (ofNP F (q + p)).add_witnessLength_le n
      change n + (q + p).eval n ≤ NPVerifier.width F (q + p) n at this
      rw [Polynomial.eval_add] at this
      change n + q.eval n + j < NPVerifier.width F (q + p) n
      omega
    · exact (ofNP F (q + p)).wellFormed n g hg
  witnessLength n := q.eval n
  computableInPolyTime_witnessLength := by fun_prop
  add_witnessLength_le n := by
    have := (ofNP F (q + p)).add_witnessLength_le n
    change n + (q + p).eval n ≤ NPVerifier.width F (q + p) n at this
    rw [Polynomial.eval_add] at this
    change n + q.eval n ≤ NPVerifier.width F (q + p) n
    omega

/-- The NP verifier's circuit, run on the word `x ++ w` for a proof `w` of the right length,
accepts as `F` does on `frame x ++ w`. -/
theorem measureProb_ofNP_inputState (F : UniformCircuitFamily) (p : Polynomial ℕ) (x w : List Bool)
    (hw : w.length = p.eval x.length) :
    measureProb (Circuit.eval (Circuit.ofCodes (NPVerifier.width F p x.length)
      (NPVerifier.gates F p x.length)) (ket (inputState _ (x ++ w))))
      (accepting (NPVerifier.width F p x.length)) = F.acceptProb (frame x ++ w) := by
  have hofFn : List.ofFn (fun i : Fin ((ofNP F p).witnessLength x.length) => w.getD i false) =
      w := by
    refine List.ext_getElem (by rw [List.length_ofFn, hw]; rfl) fun i h₁ h₂ => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  have := acceptProb_ofNP_ket F p x fun i => w.getD i false
  rw [acceptProb_ket, hofFn] at this
  exact this

/-- **The acceptance probability of the Merlin–Arthur verifier.** When `F` decides `f` exactly on
the words `frame x ++ w`, the verifier accepts the witness state `ψ = ∑_y ψ_y |y⟩` with probability
`∑_y |ψ_y|² · #{r | f (y ++ r)} / 2^{p(|x|)}`: the coins are uniform and independent of the proof,
and different basis proofs do not interfere. -/
theorem acceptProb_ofMA (F : UniformCircuitFamily) (q p : Polynomial ℕ) (x : List Bool)
    (f : List Bool → Bool)
    (hF : ∀ w : List Bool, w.length = (q + p).eval x.length →
      F.acceptProb (frame x ++ w) = if f w then 1 else 0)
    (ψ : Qubits (q.eval x.length)) :
    (ofMA F q p).acceptProb x ψ = ∑ y, ‖ψ.ofLp y‖ ^ 2 *
      ((univ.filter fun r : Fin (p.eval x.length) → Bool => f (List.ofFn y ++ List.ofFn r)).card /
        2 ^ p.eval x.length) := by
  set N := NPVerifier.width F (q + p) x.length
  have hp : x.length + q.eval x.length + p.eval x.length ≤ N := by
    have := (ofNP F (q + p)).add_witnessLength_le x.length
    change x.length + (q + p).eval x.length ≤ N at this
    rw [Polynomial.eval_add] at this
    omega
  have hq : x.length + q.eval x.length ≤ N := by omega
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  set X : (Fin (q.eval x.length) → Bool) × (Fin (p.eval x.length) → Bool) → Fin N → Bool :=
    fun yr => inputState N (x ++ List.ofFn yr.1 ++ List.ofFn yr.2)
  have hX (yr : (Fin (q.eval x.length) → Bool) × (Fin (p.eval x.length) → Bool)) :
      X yr = glue (blockEmb _ hp) yr.2 (glue (blockEmb _ hq) yr.1 (inputState N x)) := by
    rw [glue_blockEmb_inputState hq x rfl, glue_blockEmb_inputState hp _ (by simp)]
  have hXinj : Function.Injective X := by
    rintro ⟨y, r⟩ ⟨y', r'⟩ h
    rw [hX, hX] at h
    have hr : r = r' := by
      have := congrArg (· ∘ blockEmb _ hp) h
      simpa using this
    subst hr
    have hy : y = y' := by
      funext i
      have hne : ∀ j, blockEmb _ hp j ≠ blockEmb _ hq i := fun j hj => by
        have := congrArg Fin.val hj
        simp only [blockEmb_apply_val] at this
        omega
      have := congrFun h (blockEmb _ hq i)
      rwa [glue_of_not _ _ _ hne, glue_of_not _ _ _ hne, glue_apply_emb, glue_apply_emb] at this
    rw [hy]
  have hv : Orthonormal ℂ fun yr => ket (X yr) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℂ)).comp X hXinj
  have hstate : Circuit.eval (Circuit.ofCodes N (hadamardCodes (x.length + q.eval x.length)
      (p.eval x.length))) (embedState (blockEmb x.length hq) (inputState N x) ψ) =
      ∑ yr, (ψ.ofLp yr.1 * s ^ p.eval x.length) • ket (X yr) := by
    rw [embedState_eq_sum, map_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun y _ => ?_
    rw [map_smul, glue_blockEmb_inputState hq x rfl y,
      eval_hadamardCodes_ket hp _ fun i => ?_, smul_sum]
    · refine sum_congr rfl fun r _ => ?_
      rw [smul_smul, glue_blockEmb_inputState hp _ (by simp) r]
    · rw [inputState, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
      rfl
  set U := (Circuit.eval (Circuit.ofCodes N (NPVerifier.gates F (q + p) x.length))).toLinearIsometry
  have hyr (yr : (Fin (q.eval x.length) → Bool) × (Fin (p.eval x.length) → Bool)) :
      measureProb (U (ket (X yr))) (accepting N) =
        if f (List.ofFn yr.1 ++ List.ofFn yr.2) then 1 else 0 := by
    have hlen : (List.ofFn yr.1 ++ List.ofFn yr.2).length = (q + p).eval x.length := by
      simp [Polynomial.eval_add]
    rw [← hF _ hlen, ← measureProb_ofNP_inputState F (q + p) x _ hlen, ← List.append_assoc]
    rfl
  have key := measureProb_map_sum_orthonormal U hv (fun yr => ψ.ofLp yr.1 * s ^ p.eval x.length)
    (accepting N) (fun yr => f (List.ofFn yr.1 ++ List.ofFn yr.2) = true)
    (fun yr h => by rw [hyr, ite_eq_left_iff.mpr fun h' => absurd h h'])
    (fun yr h => by rw [hyr, ite_eq_right_iff.mpr fun h' => absurd h' h])
  have hmain : measureProb (Circuit.eval (Circuit.ofCodes N (MAVerifier.gates F q p x.length))
      (embedState (blockEmb x.length hq) (inputState N x) ψ)) (accepting N) =
      ∑ yr ∈ univ.filter fun yr : (Fin (q.eval x.length) → Bool) × (Fin (p.eval x.length) → Bool)
        => f (List.ofFn yr.1 ++ List.ofFn yr.2) = true,
        ‖ψ.ofLp yr.1 * s ^ p.eval x.length‖ ^ 2 := by
    rw [MAVerifier.gates, Circuit.ofCodes_append, Circuit.eval_append, hstate]
    exact key
  rw [show (ofMA F q p).acceptProb x ψ = measureProb (Circuit.eval (Circuit.ofCodes N
    (MAVerifier.gates F q p x.length)) (embedState (blockEmb x.length hq) (inputState N x) ψ))
    (accepting N) from rfl, hmain]
  have hs : ‖s ^ p.eval x.length‖ ^ 2 = 1 / 2 ^ p.eval x.length := by
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt (by norm_num), one_div, inv_pow]
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  simp only [norm_mul, mul_pow, hs]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- **A basis proof** `y` is accepted with probability `#{r | f (y ++ r)} / 2^{p(|x|)}`. -/
theorem acceptProb_ofMA_ket (F : UniformCircuitFamily) (q p : Polynomial ℕ) (x : List Bool)
    (f : List Bool → Bool)
    (hF : ∀ w : List Bool, w.length = (q + p).eval x.length →
      F.acceptProb (frame x ++ w) = if f w then 1 else 0)
    (y : Fin (q.eval x.length) → Bool) :
    (ofMA F q p).acceptProb x (ket y) =
      (univ.filter fun r : Fin (p.eval x.length) → Bool => f (List.ofFn y ++ List.ofFn r)).card /
        2 ^ p.eval x.length := by
  refine (acceptProb_ofMA F q p x f hF (ket y)).trans ?_
  rw [sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp

/-- **Soundness of the Merlin–Arthur verifier**: if every basis proof is accepted with probability
at most `t`, then so is every unit witness state. -/
theorem acceptProb_ofMA_le (F : UniformCircuitFamily) (q p : Polynomial ℕ) (x : List Bool)
    (f : List Bool → Bool)
    (hF : ∀ w : List Bool, w.length = (q + p).eval x.length →
      F.acceptProb (frame x ++ w) = if f w then 1 else 0) {t : ℝ}
    (ht : ∀ y : Fin (q.eval x.length) → Bool,
      ((univ.filter fun r : Fin (p.eval x.length) → Bool => f (List.ofFn y ++ List.ofFn r)).card /
        2 ^ p.eval x.length : ℝ) ≤ t)
    (ψ : Qubits (q.eval x.length)) (hψ : ‖ψ‖ = 1) :
    (ofMA F q p).acceptProb x ψ ≤ t := by
  rw [acceptProb_ofMA F q p x f hF]
  calc _ ≤ ∑ y, ‖ψ.ofLp y‖ ^ 2 * t :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ht y) (by positivity)
    _ = t := by rw [← sum_mul, ← EuclideanSpace.norm_sq_eq, hψ, one_pow, one_mul]

end UniformVerifierFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

private theorem two_thirds_le_div {m c : ℕ} (h : 2 * 2 ^ m ≤ 3 * c) :
    (2 / 3 : ℝ) ≤ c / 2 ^ m := by
  rw [le_div_iff₀ (by positivity)]
  have : (2 * 2 ^ m : ℝ) ≤ 3 * c := by exact_mod_cast h
  linarith

private theorem div_le_one_third {m : ℕ} (g : (Fin m → Bool) → Bool)
    (h : 2 * 2 ^ m ≤ 3 * (univ.filter fun r => g r = false).card) :
    ((univ.filter fun r => g r = true).card / 2 ^ m : ℝ) ≤ 1 / 3 := by
  have hsum := card_filter_add_card_filter_not (s := univ) fun r => g r = true
  simp only [Bool.not_eq_true] at hsum
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hsum
  rw [div_le_iff₀ (by positivity)]
  have h₁ : (2 * 2 ^ m : ℝ) ≤ 3 * (univ.filter fun r => g r = false).card := by exact_mod_cast h
  have h₂ : ((univ.filter fun r => g r = true).card : ℝ) +
      (univ.filter fun r => g r = false).card = 2 ^ m := by exact_mod_cast hsum
  linarith

/-- **`MA ⊆ QMA`**: Merlin's proof is read as a quantum witness and Arthur's coins are prepared
with Hadamard gates. A basis state of a good proof is accepted with probability at least `2 / 3`;
a witness state `∑_y ψ_y |y⟩` is accepted with the average of the acceptance probabilities of the
proofs `y`, weighted by `|ψ_y|²`, which is at most `1 / 3` on a non-member. -/
theorem MA_subset_QMA : MA enc ⊆ QMA enc := by
  rintro A ⟨q, p, V, hV, hA⟩
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  refine mem_QMA.mpr ⟨UniformVerifierFamily.ofMA F q p, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ?_⟩⟩
  · obtain ⟨y, hy⟩ := (hA a).1 ha
    exact ⟨ket y, norm_ket _, (two_thirds_le_div hy).trans_eq
      (UniformVerifierFamily.acceptProb_ofMA_ket F q p (enc a) _ (fun w _ => hF (a, w)) y).symm⟩
  · exact UniformVerifierFamily.acceptProb_ofMA_le F q p (enc a) _ (fun w _ => hF (a, w))
      (fun y => div_le_one_third _ ((hA a).2 ha y)) ψ hψ

/-- **`BPP ⊆ BQP`**: the coins of a bounded-error verifier are prepared with Hadamard gates and the
verifier runs as a reversible circuit; this is the Merlin–Arthur verifier with no proof. -/
theorem BPP_subset_BQP : BPP enc ⊆ BQP enc := by
  rintro A ⟨p, V, hV, hA⟩
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  have hacc (a : α) : (UniformVerifierFamily.ofMA F 0 p).toUniformCircuitFamily.acceptProb (enc a) =
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool => V (a, List.ofFn r)).card /
        2 ^ p.eval (enc a).length := by
    have h₁ := (UniformVerifierFamily.ofMA F 0 p).acceptProb_ket_of_witnessLength_eq_zero (enc a)
      (Polynomial.eval_zero) default
    have h₂ := UniformVerifierFamily.acceptProb_ofMA_ket F 0 p (enc a) (fun w => V (a, w))
      (fun w _ => hF (a, w)) default
    rw [List.eq_nil_of_length_eq_zero (by simp : (List.ofFn
      (default : Fin ((0 : Polynomial ℕ).eval (enc a).length) → Bool)).length = 0)] at h₂
    simp only [List.nil_append] at h₂
    exact h₁.symm.trans h₂
  refine ⟨(UniformVerifierFamily.ofMA F 0 p).toUniformCircuitFamily, fun a => ⟨fun ha => ?_,
    fun ha => ?_⟩⟩
  · rw [hacc]
    exact two_thirds_le_div ((hA a).1 ha)
  · rw [hacc]
    exact div_le_one_third (fun r => V (a, List.ofFn r)) ((hA a).2 ha)

end Cslib.Complexity
