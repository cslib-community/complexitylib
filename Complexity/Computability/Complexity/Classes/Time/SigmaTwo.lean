/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.LinearClock
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Tactic.EncLen

/-!
# Two-quantifier alternating time

`Cslib.Complexity.SigmaTwoTIME enc t` consists of the problems `A` with a verifier `V`, computable
within linear time and space on the encoded triples `(a, (u, v))`, and a constant `c` such that,
for every certificate length `L ≥ c * t n + c`, where `n` is the length of the encoded instance,
`a ∈ A` exactly when some `u` of length `L` makes `V (a, (u, v))` true for every `v` of length `L`.
This is the class `Σ₂TIME(t)` of [Arora and Barak, Section 5.4][AroraBarak09], in the verifier
form of `Cslib.Complexity.exists_verifier_of_mem_NTIME`: the certificate blocks are as long as the
alternating computation, and the verifier pays linearly for reading them. Informally, for
time-constructible `t` with `t n ≥ n`, this is the class of problems decided by alternating machines
within time `O(t n)` that start existentially and alternate at most once; there is no Lean bridge to
`Turing.MultiTapeATM`. Below linear time the classes differ, since the verifier always reads the
instance: `Σ₂TIME(0)` contains linear deterministic time.

Every certificate length above the threshold works, so that the class is monotone in `t` and so
that a verifier is linear on every input, also on certificates too short to pay for the
verification (`Turing.MultiTapeTM.ComputableInO.exists_linear_eq_of_time_le`). Both properties are
needed when an inclusion `NTIME(n) ⊆ DTIME(t')` is applied to the universal block of a
`Σ₂TIME` verifier, in the slowdown step of the time–space lower bounds for nondeterministic linear
time (`Cslib.Complexity.SigmaTwoTIME_subset_NTIME`).

The union over polynomial bounds is the second level `Σ₂ᵖ` of the polynomial hierarchy
(`Cslib.Complexity.mem_SigmaP_two_iff_exists_mem_SigmaTwoTIME`).

## Main definitions

* `Cslib.Complexity.SigmaTwoTIME`: two-quantifier alternating time, starting existentially.

## Main results

* `Cslib.Complexity.mem_SigmaTwoTIME_iff`: membership through a verifier and a threshold.
* `Cslib.Complexity.mem_SigmaTwoTIME_of_time_le`: a verifier that is linear once the certificates
  are long enough suffices.
* `Cslib.Complexity.SigmaTwoTIME_mono`, `Cslib.Complexity.SigmaTwoTIME_mono_of_le_mul_add`:
  monotonicity.
* `Cslib.Complexity.NTIME_subset_SigmaTwoTIME`,
  `Cslib.Complexity.compl_mem_SigmaTwoTIME_of_mem_NTIME`: nondeterministic and
  co-nondeterministic time are in `Σ₂TIME`.
* `Cslib.Complexity.mem_SigmaP_two_iff_exists_mem_SigmaTwoTIME`: `Σ₂ᵖ = ⋃ₖ Σ₂TIME(n ^ k)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Two-quantifier alternating time** `Σ₂TIME(t)`: the problems `A` with a verifier `V`,
computable within linear time and space on the encoded triples `(a, (u, v))`, and a constant `c`
such that for every certificate length `L ≥ c * t n + c`, where `n` is the length of the encoded
instance, `a ∈ A` iff `∃ u, ∀ v, V (a, (u, v)) = true` over the words `u` and `v` of length `L`. -/
def SigmaTwoTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (V : α × (List Bool × List Bool) → Bool) (c : ℕ),
    ComputableInO V (encPair enc (encPair encBits encBits)) encBool
      (fun x => (encPair enc (encPair encBits encBits) x).length)
      (fun x => (encPair enc (encPair encBits encBits) x).length) ∧
    ∀ a L, c * t (enc a).length + c ≤ L →
      (a ∈ A ↔ ∃ u : List Bool, u.length = L ∧
        ∀ v : List Bool, v.length = L → V (a, (u, v)) = true)}

/-- Membership in `Σ₂TIME`: a verifier, linear on the encoded triples, and a threshold above which
every certificate length decides membership. -/
theorem mem_SigmaTwoTIME_iff {A : Set α} {t : ℕ → ℕ} : A ∈ SigmaTwoTIME enc t ↔
    ∃ (V : α × (List Bool × List Bool) → Bool) (c : ℕ),
      ComputableInO V (encPair enc (encPair encBits encBits)) encBool
        (fun x => (encPair enc (encPair encBits encBits) x).length)
        (fun x => (encPair enc (encPair encBits encBits) x).length) ∧
      ∀ a L, c * t (enc a).length + c ≤ L →
        (a ∈ A ↔ ∃ u : List Bool, u.length = L ∧
          ∀ v : List Bool, v.length = L → V (a, (u, v)) = true) :=
  Iff.rfl

/-- **Membership in `Σ₂TIME` from a verifier that is linear once the certificates are long
enough.** The verifier may take any time `T`, provided `T` is linear on the triples whose
certificates have the length `L ≥ c * t n + c` of the membership condition. -/
theorem mem_SigmaTwoTIME_of_time_le {A : Set α} {t : ℕ → ℕ}
    {V : α × (List Bool × List Bool) → Bool} {T S : α × (List Bool × List Bool) → ℕ} {c K : ℕ}
    (hV : ComputableInO V (encPair enc (encPair encBits encBits)) encBool T S)
    (hT : ∀ a L, c * t (enc a).length + c ≤ L → ∀ u v : List Bool, u.length = L →
      v.length = L →
        T (a, (u, v)) ≤ K * (encPair enc (encPair encBits encBits) (a, (u, v))).length + K)
    (hA : ∀ a L, c * t (enc a).length + c ≤ L →
      (a ∈ A ↔ ∃ u : List Bool, u.length = L ∧ ∀ v : List Bool, v.length = L →
        V (a, (u, v)) = true)) :
    A ∈ SigmaTwoTIME enc t := by
  obtain ⟨g, hg, hgV⟩ := hV.exists_linear_eq_of_time_le K
  refine ⟨g, c, hg, fun a L hL => (hA a L hL).trans ?_⟩
  refine exists_congr fun u => and_congr_right fun hu => forall_congr' fun v =>
    forall_congr' fun hv => ?_
  rw [hgV _ (hT a L hL u v hu hv)]

/-- `Σ₂TIME` depends on the time bound only up to a constant factor and an additive constant. -/
theorem SigmaTwoTIME_mono_of_le_mul_add {t₁ t₂ : ℕ → ℕ} {C : ℕ}
    (h : ∀ n, t₁ n ≤ C * t₂ n + C) : SigmaTwoTIME enc t₁ ⊆ SigmaTwoTIME enc t₂ := by
  rintro A ⟨V, c, hV, hA⟩
  refine ⟨V, c * C + c, hV, fun a L hL => hA a L ?_⟩
  have := Nat.mul_le_mul_left c (h (enc a).length)
  rw [Nat.mul_add, ← Nat.mul_assoc] at this
  rw [Nat.add_mul] at hL
  omega

/-- `Σ₂TIME` is monotone in the time bound. -/
theorem SigmaTwoTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    SigmaTwoTIME enc t₁ ⊆ SigmaTwoTIME enc t₂ :=
  SigmaTwoTIME_mono_of_le_mul_add (C := 1) fun n => by have := h n; omega

/-- The projection forgetting one certificate block, within linear time and space. -/
private theorem computableInO_dropBlock (second : Bool) :
    ComputableInO (fun x : α × (List Bool × List Bool) => (x.1, if second then x.2.2 else x.2.1))
      (encPair enc (encPair encBits encBits)) (encPair enc encBits)
      (fun x => (encPair enc (encPair encBits encBits) x).length)
      (fun x => (encPair enc (encPair encBits encBits) x).length) := by
  have hpair := ComputableInO.snd enc (encPair encBits encBits)
  have hblock : ComputableInO (fun x : α × (List Bool × List Bool) =>
      if second then x.2.2 else x.2.1) (encPair enc (encPair encBits encBits)) encBits
      (fun x => (encPair enc (encPair encBits encBits) x).length)
      (fun x => (encPair enc (encPair encBits encBits) x).length) := by
    cases second
    · exact (ComputableInO.fst encBits encBits).comp_linear hpair
    · exact (ComputableInO.snd encBits encBits).comp_linear hpair
  exact ((ComputableInO.fst enc (encPair encBits encBits)).prod hblock).mono 2
    (fun x => by omega) fun x => by omega

/-- **Nondeterministic time is in `Σ₂TIME`**, with a universal block that the verifier ignores. -/
theorem NTIME_subset_SigmaTwoTIME {t : ℕ → ℕ} : NTIME enc t ⊆ SigmaTwoTIME enc t := by
  intro A hA
  obtain ⟨V, c, hV, hA⟩ := exists_verifier_of_mem_NTIME hA
  refine ⟨V ∘ fun x => (x.1, x.2.1), c, hV.comp_linear (computableInO_dropBlock false),
    fun a L hL => (hA a L hL).trans ?_⟩
  refine exists_congr fun u => and_congr_right fun hu => ⟨fun h v _ => h, fun h => ?_⟩
  exact h (List.replicate L false) List.length_replicate

/-- **Co-nondeterministic time is in `Σ₂TIME`**, with an existential block that the verifier
ignores. -/
theorem compl_mem_SigmaTwoTIME_of_mem_NTIME {t : ℕ → ℕ} {A : Set α}
    (hA : A ∈ NTIME enc t) :
    Aᶜ ∈ SigmaTwoTIME enc t := by
  obtain ⟨V, c, hV, hA⟩ := exists_verifier_of_mem_NTIME hA
  refine ⟨fun x => !V (x.1, x.2.2), c,
    (hV.comp_linear (computableInO_dropBlock true)).not', fun a L hL => ?_⟩
  rw [Set.mem_compl_iff, hA a L hL]
  simp only [not_exists, not_and, Bool.not_eq_eq_eq_not, Bool.not_true]
  exact ⟨fun h => ⟨List.replicate L false, List.length_replicate,
    fun v hv => Bool.eq_false_iff.mpr (h v hv)⟩,
    fun ⟨_, _, h⟩ v hv => Bool.eq_false_iff.mp (h v hv)⟩

/-! ### The second level of the polynomial hierarchy -/

/-- A problem in `Σ₂TIME(n ^ k)` is in `Σ₂ᵖ`: cut the concatenated certificate of `Σ₂ᵖ` into the
two blocks of equal length `c * n ^ k + c`. -/
theorem mem_SigmaP_two_of_mem_SigmaTwoTIME {A : Set α} {k : ℕ}
    (hA : A ∈ SigmaTwoTIME enc (· ^ k)) : A ∈ SigmaP 2 enc := by
  obtain ⟨V, c, hV, hA⟩ := hA
  set p : Polynomial ℕ := Polynomial.C c * Polynomial.X ^ k + Polynomial.C c
  have hp (n : ℕ) : p.eval n = c * n ^ k + c := by simp [p]
  refine ⟨[p, p], fun x => V (x.1, (x.2.take (p.eval (enc x.1).length),
    x.2.drop (p.eval (enc x.1).length))), rfl, ?_, fun a => ?_⟩
  · have hVp : ComputableInPolyTime V (encPair enc (encPair encBits encBits)) encBool :=
      hV.computableInPolyTime .self .self
    have hn : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
    exact hVp.comp ((ComputableInPolyTime.fst enc encBits).prod
      ((ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.snd enc encBits) hn).prod
        (ComputableInPolyTime.bitsDropWithInput (ComputableInPolyTime.snd enc encBits) hn)))
  · rw [hA a _ (hp _).ge]
    simp only [List.map_cons, List.map_nil, alternation_true_cons,
      alternation_false_cons, alternation_nil, List.append_nil]
    refine exists_congr fun u => and_congr_right fun hu => forall_congr' fun v =>
      forall_congr' fun _ => ?_
    rw [List.take_left' hu, List.drop_left' hu]

/-- Cut the two blocks of a `Σ₂TIME` certificate to the lengths `P₁` and `P₂` of the blocks of a
`Σ₂ᵖ` certificate, and concatenate them. -/
private def cutBlocks (P₁ P₂ : ℕ) (u v : List Bool) : List Bool := u.take P₁ ++ v.take P₂

/-- Evaluating a polynomial at the length of the encoded instance, in unary, within time and
space polynomial in that length plus the input length. -/
private theorem exists_computableInO_eval (p : Polynomial ℕ) :
    ∃ c d : ℕ, ∃ S : α × (List Bool × List Bool) → ℕ,
      ComputableInO (fun x : α × (List Bool × List Bool) => p.eval (enc x.1).length)
        (encPair enc (encPair encBits encBits)) encUnary
        (fun x => (encPair enc (encPair encBits encBits) x).length +
          c * ((enc x.1).length + 1) ^ d) S := by
  obtain ⟨T, S, hT, -, h⟩ := (ComputableInPolyTime.unary_eval p).exists_computableInO
  obtain ⟨c, d, hc⟩ := hT.exists_le
  have hn : ComputableInO (fun x : α × (List Bool × List Bool) => (enc x.1).length)
      (encPair enc (encPair encBits encBits)) encUnary
      (fun x => (encPair enc (encPair encBits encBits) x).length)
      (fun x => (encPair enc (encPair encBits encBits) x).length) :=
    (ComputableInO.lengthUnary.comp_enc enc).comp_linear (ComputableInO.fst enc _)
  refine ⟨c, d, _, (h.comp hn).mono_time 1 fun x => ?_⟩
  have := hc (enc x.1).length
  enc_len at this

/-- A problem in `Σ₂ᵖ` is in `Σ₂TIME(n ^ k)` for some `k`: pad both blocks to a common length,
and let the verifier cut them back. Cutting is linear, and the original verifier then runs within
a polynomial of the instance length alone, so that the verifier is linear once the common length
exceeds that polynomial. -/
theorem exists_mem_SigmaTwoTIME_of_mem_SigmaP_two {A : Set α} (hA : A ∈ SigmaP 2 enc) :
    ∃ k, A ∈ SigmaTwoTIME enc (· ^ k) := by
  obtain ⟨ps, V, hlen, hV, hA⟩ := hA
  obtain ⟨p₁, p₂, rfl⟩ : ∃ p₁ p₂, ps = [p₁, p₂] := by
    match ps, hlen with
    | [p₁, p₂], _ => exact ⟨p₁, p₂, rfl⟩
  obtain ⟨TV, SV, hTV, -, hVO⟩ := hV.exists_computableInO
  obtain ⟨cV, dV, hcV⟩ := hTV.exists_le
  obtain ⟨c₁, d₁, S₁, h₁⟩ := exists_computableInO_eval (enc := enc) p₁
  obtain ⟨c₂, d₂, S₂, h₂⟩ := exists_computableInO_eval (enc := enc) p₂
  -- the cut blocks, within linear time plus polynomials of the instance length
  have hu := ComputableInO.of_linear ComputableInDegree.bitsTake |>.comp
    (((ComputableInO.fst encBits encBits).comp_linear (ComputableInO.snd enc _)).prod h₁)
  have hv := ComputableInO.of_linear ComputableInDegree.bitsTake |>.comp
    (((ComputableInO.snd encBits encBits).comp_linear (ComputableInO.snd enc _)).prod h₂)
  have hcut := hu.append hv (encOut := encBits)
    (g := fun x : α × (List Bool × List Bool) =>
      cutBlocks (p₁.eval (enc x.1).length) (p₂.eval (enc x.1).length) x.2.1 x.2.2)
    fun _ => rfl
  have hW := hVO.comp ((ComputableInO.fst enc _).prod hcut)
  -- the polynomial of the instance length that the certificates must exceed
  obtain ⟨c₀, d₀, hR⟩ : ∃ c₀ d₀ : ℕ, ∀ n,
      4 * (c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂) + p₁.eval n + p₂.eval n +
        cV * (2 * n + 2 + p₁.eval n + p₂.eval n + 1) ^ dV ≤ c₀ * (n + 1) ^ d₀ :=
    Cslib.polynomiallyBounded_iff_le.mp (by fun_prop)
  have hRL (a : α) (L : ℕ) (hL : c₀ * 2 ^ d₀ * (enc a).length ^ d₀ + c₀ * 2 ^ d₀ ≤ L) :
      4 * (c₁ * ((enc a).length + 1) ^ d₁ + c₂ * ((enc a).length + 1) ^ d₂) +
        p₁.eval (enc a).length + p₂.eval (enc a).length +
        cV * (2 * (enc a).length + 2 + p₁.eval (enc a).length + p₂.eval (enc a).length + 1) ^ dV
        ≤ L := by
    have h₁ := hR (enc a).length
    have h₂ := Nat.mul_add_one_pow_le_two_pow c₀ d₀ (enc a).length
    have h₃ : c₀ ≤ c₀ * 2 ^ d₀ := Nat.le_mul_of_pos_right c₀ (Nat.two_pow_pos d₀)
    omega
  refine ⟨d₀, mem_SigmaTwoTIME_of_time_le (c := c₀ * 2 ^ d₀) (K := 8) hW
    (fun a L hL u v hu hv => ?_) fun a L hL => ?_⟩
  · -- the running time
    have hRL := hRL a L hL
    have hpre : (encPair enc encBits (a, cutBlocks (p₁.eval (enc a).length)
        (p₂.eval (enc a).length) u v)).length ≤
        2 * (enc a).length + 2 + p₁.eval (enc a).length + p₂.eval (enc a).length := by
      enc_len [cutBlocks, List.length_take]
    have hTVa := (hcV (a, cutBlocks (p₁.eval (enc a).length) (p₂.eval (enc a).length) u v)).trans
      (Nat.mul_le_mul_left cV (Nat.pow_le_pow_left (Nat.add_le_add_right hpre 1) dV))
    enc_len [Function.comp_apply, hu, hv] at hTVa ⊢
  · -- correctness
    have hRL := hRL a L hL
    have hP₁ : p₁.eval (enc a).length ≤ L := by omega
    have hP₂ : p₂.eval (enc a).length ≤ L := by omega
    rw [hA a]
    simp only [List.map_cons, List.map_nil, alternation_true_cons, alternation_false_cons,
      alternation_nil, List.append_nil, Function.comp_apply, cutBlocks]
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨w ++ List.replicate (L - p₁.eval (enc a).length) false, by simp [hw]; omega,
        fun v hv => ?_⟩
      rw [List.take_left' hw]
      exact h _ (by simp [hv]; omega)
    · rintro ⟨u, hu, h⟩
      refine ⟨u.take (p₁.eval (enc a).length), by simp [hu]; omega, fun w hw => ?_⟩
      have := h (w ++ List.replicate (L - p₂.eval (enc a).length) false) (by simp [hw]; omega)
      rwa [List.take_left' hw] at this

/-- **The second level of the polynomial hierarchy is the union of `Σ₂TIME(n ^ k)`.** -/
theorem mem_SigmaP_two_iff_exists_mem_SigmaTwoTIME {A : Set α} :
    A ∈ SigmaP 2 enc ↔ ∃ k, A ∈ SigmaTwoTIME enc (· ^ k) :=
  ⟨exists_mem_SigmaTwoTIME_of_mem_SigmaP_two, fun ⟨_, h⟩ => mem_SigmaP_two_of_mem_SigmaTwoTIME h⟩

end Cslib.Complexity
