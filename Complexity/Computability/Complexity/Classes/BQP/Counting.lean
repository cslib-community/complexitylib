/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
public import Complexity.Computability.Circuit.Quantum.PathSum
public import Complexity.Computability.Complexity.Classes.AWPP
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-!
# `BQP ⊆ AWPP ⊆ PP`

The acceptance probability of a uniform family of Hadamard–Toffoli circuits is a gap function
divided by a power of two, `acceptGap / 2^h` (`Cslib.Quantum.acceptProb_eq_acceptGap`). Here both
are computed classically. The path simulation `Cslib.Quantum.pathStep` runs in polynomial time
(`Cslib.Quantum.computableInPolyTime_pathStep`), so the acceptance gap is a sum, over pairs of
polynomially long paths, of a polynomial-time integer, which is a `GapP` function; the number `h`
of Hadamard gates is computed in unary. Fenner's characterization of AWPP
(`Cslib.Complexity.AWPP`) then gives `BQP ⊆ AWPP` (`Cslib.Complexity.BQP_subset_AWPP`), and
`AWPP ⊆ PP` gives `BQP ⊆ PP` (`Cslib.Complexity.BQP_subset_PP`).

`BQP ⊆ PP` is due to Adleman, DeMarrais and Huang
[Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997]. `BQP ⊆ AWPP` is Theorem 3.1 of
[Fortnow, Rogers][FortnowRogers1999], proved there through Lemma 3.2: the acceptance probability of
a quantum Turing machine running for `t` steps, with amplitudes in `{0, ±3/5, ±4/5, ±1}`, is a GapP
function divided by `5^{2t}`. For circuits over the Hadamard and Toffoli gates the denominator is
`2^h` instead. Fortnow and Rogers work with quantum Turing machines; this file works with the
uniform circuit families of `Cslib.Complexity.BQP`.

## Main results

* `Cslib.Quantum.computableInPolyTime_pathStep`,
  `Cslib.Quantum.computableInPolyTime_foldl_pathStep`: the path simulation runs in polynomial
  time.
* `Cslib.Complexity.acceptGap_mem_GapP`: the acceptance gap of a uniform family is `GapP`.
* `Cslib.Complexity.BQP_subset_AWPP`, `Cslib.Complexity.BQP_subset_PP`.

## References

* [L. Adleman, J. DeMarrais, M.-D. Huang, *Quantum computability*][AdlemanDeMarraisHuang1997]
* [L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*][FortnowRogers1999]
* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

@[expose] public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- One simulation step, written with polynomial-time list operations. -/
private theorem pathStep_eq (p : (List Bool × List Bool × Bool) × GateCode) :
    pathStep p.1 p.2 =
      if p.2.1 then
        (if p.2.2.1 < p.1.1.length then
            p.1.1.take p.2.2.1 ++ p.1.2.1.headD false :: p.1.1.drop (p.2.2.1 + 1) else p.1.1,
          p.1.2.1.tail, p.1.2.2 ^^ (p.1.1.getD p.2.2.1 false && p.1.2.1.headD false))
      else
        (if p.2.2.1 < p.1.1.length then
            p.1.1.take p.2.2.1 ++
              (p.1.1.getD p.2.2.1 false ^^ p.2.2.2.all fun c => p.1.1.getD c false) ::
                p.1.1.drop (p.2.2.1 + 1) else p.1.1,
          p.1.2.1, p.1.2.2) := by
  obtain ⟨⟨s, π, σ⟩, ⟨_ | _, t, cs⟩⟩ := p <;>
    simp only [pathStep, List.set_eq_take_append_cons_drop] <;> rfl

/-- **The path simulation step runs in polynomial time**, with the register and the unread path
as raw bit strings. -/
theorem computableInPolyTime_pathStep :
    ComputableInPolyTime (fun p : (List Bool × List Bool × Bool) × GateCode => pathStep p.1 p.2)
      (encPair (encPair encBits (encPair encBits encBool)) encGateCode)
      (encPair encBits (encPair encBits encBool)) := by
  simp only [pathStep_eq]
  fun_prop

/-- A simulation step never lengthens the encoded state. -/
private theorem length_encPair_pathStep (st : List Bool × List Bool × Bool) (g : GateCode) :
    (encPair encBits (encPair encBits encBool) (pathStep st g)).length ≤
      (encPair encBits (encPair encBits encBool) st).length + 0 := by
  obtain ⟨s, π, σ⟩ := st
  obtain ⟨_ | _, t, cs⟩ := g <;> simp [pathStep]

/-- **The path simulation runs in polynomial time** on computed gate codes and initial states. -/
theorem computableInPolyTime_foldl_pathStep {γ : Type} {encIn : γ ↪ List Bool}
    {gs : γ → List GateCode} {init : γ → List Bool × List Bool × Bool}
    (hgs : ComputableInPolyTime gs encIn (encList encGateCode))
    (hinit : ComputableInPolyTime init encIn (encPair encBits (encPair encBits encBool))) :
    ComputableInPolyTime (fun c => (gs c).foldl pathStep (init c)) encIn
      (encPair encBits (encPair encBits encBool)) :=
  ComputableInPolyTime.foldl_of_bounded_growth hgs hinit computableInPolyTime_pathStep
    length_encPair_pathStep

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **The acceptance gap of a uniform family is a `GapP` function** of the instance. -/
theorem acceptGap_mem_GapP (F : UniformCircuitFamily) :
    (fun a => acceptGap (F.gates (enc a).length)
      (List.ofFn (inputState (F.width (enc a).length) (enc a)))) ∈ GapP enc := by
  have hgates := F.computableInPolyTime_gates
  have hwidth := F.computableInPolyTime_width
  -- the input register and the number of Hadamard gates
  let X : α → List Bool := fun a =>
    enc a ++ List.replicate (F.width (enc a).length - (enc a).length) false
  have hX : ComputableInPolyTime X enc encBits := by dsimp only [X]; fun_prop
  let h : α → ℕ := fun a => hadamardCount (F.gates (enc a).length)
  have hh : ComputableInPolyTime h enc encUnary := by
    simp only [h, hadamardCount_eq_countP]
    fun_prop
  -- the simulations along the two paths of a pair
  let run₁ : (α × List Bool) × List Bool → List Bool × List Bool × Bool := fun p =>
    (F.gates (enc p.1.1).length).foldl pathStep (X p.1.1, p.1.2, false)
  let run₂ : (α × List Bool) × List Bool → List Bool × List Bool × Bool := fun p =>
    (F.gates (enc p.1.1).length).foldl pathStep (X p.1.1, p.2, false)
  have hrun₁ : ComputableInPolyTime run₁ (encPair (encPair enc encBits) encBits)
      (encPair encBits (encPair encBits encBool)) :=
    computableInPolyTime_foldl_pathStep (by fun_prop) (by fun_prop)
  have hrun₂ : ComputableInPolyTime run₂ (encPair (encPair enc encBits) encBits)
      (encPair encBits (encPair encBits encBool)) :=
    computableInPolyTime_foldl_pathStep (by fun_prop) (by fun_prop)
  let T : (α × List Bool) × List Bool → ℤ := fun p =>
    if (run₁ p).1 = (run₂ p).1 ∧ (run₁ p).1.headD false = true then
      (if (run₁ p).2.2 ^^ (run₂ p).2.2 then -1 else 1) else 0
  have hT : T ∈ GapP (encPair (encPair enc encBits) encBits) :=
    mem_GapP_of_polyTime (by dsimp only [T]; fun_prop)
  have hinner := GapP.sum_bits_mem hT (r := fun p : α × List Bool => h p.1) (by fun_prop)
  have houter := GapP.sum_bits_mem hinner hh
  convert houter using 2 with a
  rw [ofFn_inputState (F.le_width _)]
  rfl

/-- **`BQP ⊆ AWPP`** [Fortnow, Rogers][FortnowRogers1999]: the acceptance probability of a uniform
family is a `GapP` function divided by `2^h`, with `h` computed in polynomial time. -/
theorem BQP_subset_AWPP : BQP enc ⊆ AWPP enc := by
  rintro A ⟨F, hF⟩
  refine mem_AWPP_of_polyTime_exponent (acceptGap_mem_GapP F)
    (r := fun a => hadamardCount (F.gates (enc a).length))
    (by
      have := F.computableInPolyTime_gates
      simp only [hadamardCount_eq_countP]
      fun_prop) (fun a => ?_)
  have hp := acceptProb_eq_acceptGap (F.width_pos (enc a).length) _
    (F.wellFormed (enc a).length) (enc a)
  set g := acceptGap (F.gates (enc a).length)
    (List.ofFn (inputState (F.width (enc a).length) (enc a)))
  set r := hadamardCount (F.gates (enc a).length)
  have hpos : (0 : ℝ) < 2 ^ r := by positivity
  have h0 := F.acceptProb_nonneg (enc a)
  have h1 := F.acceptProb_le_one (enc a)
  change F.acceptProb (enc a) = _ at hp
  rw [hp, le_div_iff₀ hpos, zero_mul] at h0
  rw [hp, div_le_iff₀ hpos, one_mul] at h1
  refine ⟨⟨by exact_mod_cast h0, by exact_mod_cast h1⟩, fun ha => ?_, fun ha => ?_⟩
  · have := (hF a).1 ha
    rw [hp, le_div_iff₀ hpos] at this
    have : (2 : ℝ) * 2 ^ r ≤ 3 * g := by linarith
    exact_mod_cast this
  · have := (hF a).2 ha
    rw [hp, div_le_iff₀ hpos] at this
    have : (3 : ℝ) * g ≤ 2 ^ r := by linarith
    exact_mod_cast this

/-- **`BQP ⊆ PP`** [Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997]. -/
theorem BQP_subset_PP : BQP enc ⊆ PP enc :=
  fun _ hA => AWPP_subset_PP (BQP_subset_AWPP hA)

end Cslib.Complexity
