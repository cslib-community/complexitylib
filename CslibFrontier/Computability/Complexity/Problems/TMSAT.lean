/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# TMSAT is NP-complete

`TMSAT` [Arora and Barak, draft, Theorem 2.9][AroraBarak07] is the set of instances
`⟨α, x, 1ⁿ, 1ᵗ⟩` (`Cslib.Complexity.TMSATInstance`) such that some witness `u` of exactly `n` bits
makes the machine described by `α` accept the pair `⟨x, u⟩` within `t` steps.

* Machines are the library's native binary multi-tape machines, described by
  `Turing.MultiTapeTM.Universal.Desc`, and run by the universal interpreter
  `Turing.MultiTapeTM.Universal.universal`. *Accepting* means having halted with the output
  `[true]` after the given number of steps (`Cslib.Complexity.TMSATInstance.Accepts`). On the
  description of a machine this is the machine's own run
  (`Cslib.Complexity.TMSATInstance.accepts_desc_iff`). Every description is meaningful: the
  interpreter is total.
* The pair `⟨x, u⟩` is `encPair encBits encBits (x, u) = frame x ++ u`, the pairing that `NP`
  verifiers read.
* Instances are encoded by `Cslib.Complexity.encTMSATInstance` as the tuple of the description
  (`Turing.MultiTapeTM.Universal.eDesc`), the input bits, and the witness length and the step
  bound **in unary**, as `1ⁿ` and `1ᵗ` in the source. With a binary step bound the problem is
  complete for exponential time instead (`Cslib.Complexity.BoundedHalting`).

**Membership in `NP`** (`Cslib.Complexity.TMSAT.mem_NP`): the verifier reads the first `n` bits of
a certificate of length `|enc a|`, which is at least `n` as the witness length is written in unary,
and runs the interpreter for `t` steps, which is polynomial in the instance with `t` in unary
(`Turing.MultiTapeTM.Universal.computableInPolyTime_universal`).

**Hardness** (`Cslib.Complexity.TMSAT.npHard`): a problem in `NP enc` has a verifier computed by a
machine within time `c (n + 1) ^ d` on inputs of length `n`, with certificates of length
`p |enc a|`. The instance `a` maps to the description of that machine, the input `enc a`, the
witness length `p |enc a|` and the step bound `c (2 |enc a| + p |enc a| + 2) ^ d`, which bounds the
running time on every certificate of the prescribed length.

## Main definitions

* `Cslib.Complexity.TMSATInstance`: instances `⟨α, x, 1ⁿ, 1ᵗ⟩`.
* `Cslib.Complexity.encTMSATInstance`: their encoding.
* `Cslib.Complexity.TMSATInstance.Accepts`: acceptance of a witness.
* `Cslib.Complexity.TMSAT`: the language.
* `Cslib.Complexity.TMSAT.verifier`: its verifier.

## Main results

* `Cslib.Complexity.TMSATInstance.accepts_desc_iff`: acceptance on the description of a machine.
* `Cslib.Complexity.TMSAT.mem_NP`: `TMSAT` is in `NP`.
* `Cslib.Complexity.TMSAT.npHard`: every `NP` problem reduces to `TMSAT`.
* `Cslib.Complexity.TMSAT.npComplete`: `TMSAT` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

public section

namespace Cslib.Complexity

/-- An instance `⟨α, x, 1ⁿ, 1ᵗ⟩` of `Cslib.Complexity.TMSAT`
[Arora and Barak, draft, Theorem 2.9][AroraBarak07]. -/
structure TMSATInstance where
  /-- The description `α` of the machine. -/
  machine : Desc
  /-- The input `x`. -/
  input : List Bool
  /-- The length `n` of the witnesses. -/
  witnessLength : ℕ
  /-- The step bound `t`. -/
  steps : ℕ

/-- Encoding of `TMSATInstance` as the tuple of the description, the input bits, and the witness
length and the step bound in unary. -/
enc_structure encTMSATInstance : TMSATInstance where
  machine : eDesc,
  input : encBits,
  witnessLength : encUnary,
  steps : encUnary

attribute [fun_prop] encTMSATInstance_machine_polyTime encTMSATInstance_input_polyTime
  encTMSATInstance_witnessLength_polyTime encTMSATInstance_steps_polyTime
  encTMSATInstance_mk_polyTime

namespace TMSATInstance

/-- The witness `u` makes the machine of `a` accept `⟨a.input, u⟩ = frame a.input ++ u`: run by the
universal interpreter for `a.steps` steps, it has halted with the output `[true]`. -/
def Accepts (a : TMSATInstance) (u : List Bool) : Prop :=
  universal (a.machine, (encPair encBits encBits (a.input, u)).map eBit, a.steps) =
    ([eBit true], true)

/-- **Acceptance on the description of a machine**: the machine, run on `⟨x, u⟩` for `t` steps,
has halted with output `[true]`. -/
theorem accepts_desc_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n t : ℕ) (u : List Bool) :
    (⟨desc eS eBit tm, x, n, t⟩ : TMSATInstance).Accepts u ↔
      (tm.runFrom (tm.initCfg (encPair encBits encBits (x, u))) t).Halted ∧
        (tm.runFrom (tm.initCfg (encPair encBits encBits (x, u))) t).output = [true] := by
  rw [Accepts, universal_desc, Prod.mk.injEq, Cfg.Halted, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨hout, hhalt⟩
    exact ⟨hhalt, List.map_injective_iff.mpr eBit.injective (hout.trans List.map_singleton.symm)⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨by rw [hout, List.map_singleton], hhalt⟩

end TMSATInstance

/-- **TMSAT** [Arora and Barak, draft, Theorem 2.9][AroraBarak07]: the instances
`⟨α, x, 1ⁿ, 1ᵗ⟩` for which some witness `u` of exactly `n` bits makes the machine described by
`α` accept `⟨x, u⟩` within `t` steps. -/
def TMSAT : Set TMSATInstance := {a | ∃ u : List Bool, u.length = a.witnessLength ∧ a.Accepts u}

namespace TMSAT

theorem mem_iff {a : TMSATInstance} :
    a ∈ TMSAT ↔ ∃ u : List Bool, u.length = a.witnessLength ∧ a.Accepts u :=
  Iff.rfl

/-! ### Membership in `NP` -/

/-- The verifier of `TMSAT`: run the machine on `⟨x, u⟩`, where `u` is the first `n` bits of the
certificate. -/
noncomputable def verifier (q : TMSATInstance × List Bool) : Bool :=
  decide (universal (q.1.machine,
      (encPair encBits encBits (q.1.input, q.2.take q.1.witnessLength)).map eBit, q.1.steps) =
    ([eBit true], true))

theorem verifier_eq_true_iff (q : TMSATInstance × List Bool) :
    verifier q = true ↔ q.1.Accepts (q.2.take q.1.witnessLength) := by
  rw [verifier, decide_eq_true_iff, TMSATInstance.Accepts]

/-- The witness length is at most the length of the encoded instance, since it is written in
unary. -/
theorem witnessLength_le (a : TMSATInstance) : a.witnessLength ≤ (encTMSATInstance a).length := by
  simp only [encTMSATInstance_apply, encTMSATInstanceFields, length_encPair, encUnary_apply,
    List.length_replicate]
  omega

/-- `TMSAT.verifier` verifies `TMSAT` with certificates as long as the encoded instance. -/
theorem isVerifier : IsVerifier encTMSATInstance Polynomial.X verifier TMSAT :=
  IsVerifier.of_padding
    (fun a w hw hV => by
      rw [verifier_eq_true_iff] at hV
      refine ⟨w.take a.witnessLength, List.length_take_of_le ?_, hV⟩
      rw [hw, Polynomial.eval_X]
      exact witnessLength_le a)
    (fun a ⟨u, hu, hacc⟩ => ⟨u, by rw [hu, Polynomial.eval_X]; exact witnessLength_le a,
      fun k => by
        rw [verifier_eq_true_iff, ← hu, List.take_left]
        exact hacc⟩)

/-- The verifier of `TMSAT` is polynomial-time. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encTMSATInstance encBits) encBool := by
  have hpair : ComputableInPolyTime (fun p : List Bool × List Bool => encPair encBits encBits p)
      (encPair encBits encBits) encBits :=
    .of_eq fun _ => rfl
  have hin : ComputableInPolyTime
      (fun q : TMSATInstance × List Bool =>
        (q.1.machine, (encPair encBits encBits (q.1.input, q.2.take q.1.witnessLength)).map eBit,
          q.1.steps))
      (encPair encTMSATInstance encBits) eInUnary := by
    have hx : ComputableInPolyTime (fun q : TMSATInstance × List Bool =>
        encPair encBits encBits (q.1.input, q.2.take q.1.witnessLength))
        (encPair encTMSATInstance encBits) encBits :=
      hpair.comp (by fun_prop)
    have := computableInPolyTime_map_eBit.comp hx
    fun_prop
  exact (computableInPolyTime_universal.comp hin).decide_eq' (.const _)

/-- **`TMSAT` is in `NP`.** -/
theorem mem_NP : TMSAT ∈ NP encTMSATInstance :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

/-! ### Hardness -/

/-- The step bound of the reduction, `c (2 m + p m + 2) ^ d` for an instance of encoded length
`m`, as a polynomial in `m`. -/
noncomputable def stepPoly (p : Polynomial ℕ) (c d : ℕ) : Polynomial ℕ :=
  Polynomial.C c * (2 * Polynomial.X + p + 2) ^ d

theorem eval_stepPoly (p : Polynomial ℕ) (c d m : ℕ) :
    (stepPoly p c d).eval m = c * (2 * m + p.eval m + 2) ^ d := by
  simp [stepPoly]

/-- **`TMSAT` is `NP`-hard**: every problem in `NP`, with any encoding of its instances, reduces
to it in polynomial time through a machine computing its verifier. -/
theorem npHard : NPHard encTMSATInstance TMSAT := by
  intro α enc A hA
  obtain ⟨p, V, ⟨t, _, ht, -, k, State, hfin, tm, htm⟩, hV⟩ := Complexity.mem_NP.mp hA
  obtain ⟨c, d, ht⟩ := polynomiallyBounded_iff_le.mp ht
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨fun a => ⟨desc eS eBit tm, enc a, p.eval (enc a).length,
    (stepPoly p c d).eval (enc a).length⟩, ?_, fun a => ?_⟩
  · have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    have hp := (ComputableInPolyTime.unary_eval p).comp hlen
    have hq := (ComputableInPolyTime.unary_eval (stepPoly p c d)).comp hlen
    fun_prop
  · rw [hV a, mem_iff]
    refine exists_congr fun w => and_congr_right fun hw => ?_
    -- the step bound exceeds the verifier's running time on `⟨enc a, w⟩`
    have hle : t (encPair enc encBits (a, w)).length ≤ (stepPoly p c d).eval (enc a).length := by
      refine (ht _).trans_eq ?_
      rw [eval_stepPoly, length_encPair]
      simp only [encBits, Function.Embedding.refl_apply, hw]
      ring_nf
    obtain ⟨hhalt, hout⟩ := (htm (a, w)).runFrom_of_le hle
    rw [TMSATInstance.accepts_desc_iff]
    change (tm.runFrom (tm.initCfg (encPair enc encBits (a, w))) _).output = [V (a, w)] at hout
    have hx : encPair encBits encBits (enc a, w) = encPair enc encBits (a, w) := rfl
    rw [hx, hout, List.cons.injEq]
    exact ⟨fun h => ⟨hhalt, h, rfl⟩, fun h => h.2.1⟩

/-- **TMSAT is `NP`-complete** [Arora and Barak, draft, Theorem 2.9][AroraBarak07]. -/
theorem npComplete : NPComplete encTMSATInstance TMSAT :=
  ⟨mem_NP, npHard⟩

end TMSAT

end Cslib.Complexity
