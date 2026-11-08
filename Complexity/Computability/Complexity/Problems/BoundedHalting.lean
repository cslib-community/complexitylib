/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Bounded halting with a binary time bound

The instance `BoundedHalting.mk d x c = frame (eDesc d) ++ frame x ++ c` asks whether the binary
multi-tape machine described by `d` accepts the input `x` within `binaryValue c` steps, that is,
halts with the output `[true]`. The semantics is that of the universal function
`Turing.MultiTapeTM.Universal.universal`, which runs a described machine for a given number of
steps. Every bit word is read as an instance through the total decoders `unframe`, `dropFrame` and
`Turing.MultiTapeTM.Universal.decodeDesc`, so `Cslib.Complexity.BoundedHalting` is a problem on
bit words. On the descriptions of machines it means what it should
(`Cslib.Complexity.BoundedHalting.mk_desc_mem_iff`).

The step bound is written in **binary**, so it can be exponential in the length of the instance.
This makes the problem complete for exponential time under polynomial-time many-one reductions:

* It is in `E` (`Cslib.Complexity.BoundedHalting.mem_E`). The step bound of an instance `w` is
  below `2 ^ |w|`, so the simulation with the step bound capped at `2 ^ |w|` gives the same answer,
  and that simulation is polynomial in `w` padded with `2 ^ |w|`
  (`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`).
* Every problem decided within time `c₁ * 2 ^ p n + c₂`, for a polynomial-time `p`, reduces to it
  (`Cslib.Complexity.BoundedHalting.polyTimeReducible`). The reduction maps `a` to the instance
  that runs the decider on `enc a` for `2 ^ (p |enc a| + c₁ + c₂ + 1) - 1` steps, which is written
  as `p |enc a| + c₁ + c₂ + 1` ones. Taking `p n = k * n` and `p n = n ^ k` gives hardness for
  `E` and for `EXP`.

With the step bound in unary, simulation is polynomial in the length of the instance, and the
problem is in `P`. The nondeterministic version with a unary bound is `NP`-complete. The
completeness of the binary version for exponential time is standard textbook material; no
numbered source result is cited for it here.

Hence `BoundedHalting` is not in `P` (`Cslib.Complexity.BoundedHalting.notMem_P`, from
`Cslib.Complexity.P_ssubset_EXP`). Berman's theorem applies to it
(`Cslib.Complexity.BoundedHalting.not_isBiImmune_P`, in
`Complexity.Computability.Complexity.Classes.Immune.Complete`). Book's separations of `E` from
the classes closed under polynomial-time reductions, such as `NP` and `PSPACE`, are in
`Complexity.Computability.Complexity.Classes.EXP.Separation`.

## Main definitions

* `Cslib.Complexity.BoundedHalting`: bounded halting with a binary time bound.
* `Cslib.Complexity.BoundedHalting.mk`: the instance for a description, an input and a binary
  step bound.

## Main results

* `Cslib.Complexity.BoundedHalting.mk_desc_mem_iff`: on the description of a machine, membership
  is acceptance within the step bound.
* `Cslib.Complexity.BoundedHalting.mem_E`, `Cslib.Complexity.BoundedHalting.mem_EXP`: bounded
  halting is in `E`, hence in `EXP`.
* `Cslib.Complexity.BoundedHalting.polyTimeReducible`: every problem decided within time
  `c₁ * 2 ^ p n + c₂`, with `p` polynomial-time, reduces to bounded halting.
* `Cslib.Complexity.BoundedHalting.polyTimeComplete_E`,
  `Cslib.Complexity.BoundedHalting.polyTimeComplete_EXP`: bounded halting is complete for `E` and
  for `EXP` under polynomial-time many-one reductions.
* `Cslib.Complexity.BoundedHalting.notMem_P`: bounded halting is not in `P`.
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.BitString

public section

namespace Cslib.Complexity

namespace BoundedHalting

/-- The description field of a bit word read as an instance: the first framed word, decoded. -/
noncomputable def descOf (w : List Bool) : Desc := decodeDesc (unframe w)

/-- The input field of a bit word read as an instance: the second framed word. -/
def inputOf (w : List Bool) : List Bool := unframe (dropFrame w)

/-- The step bound field of a bit word read as an instance, in binary: the rest after the two
framed words. -/
def clockOf (w : List Bool) : List Bool := dropFrame (dropFrame w)

/-- The instance asking whether the machine described by `d` accepts `x` within `binaryValue c`
steps. -/
def mk (d : Desc) (x c : List Bool) : List Bool := frame (eDesc d) ++ (frame x ++ c)

@[simp]
theorem descOf_mk (d : Desc) (x c : List Bool) : descOf (mk d x c) = d :=
  decodeDesc_unframe_frame_append d _

@[simp]
theorem inputOf_mk (d : Desc) (x c : List Bool) : inputOf (mk d x c) = x := by
  rw [inputOf, mk, dropFrame_frame_append, unframe_frame_append]

@[simp]
theorem clockOf_mk (d : Desc) (x c : List Bool) : clockOf (mk d x c) = c := by
  rw [clockOf, mk, dropFrame_frame_append, dropFrame_frame_append]

/-- The step bound written in an instance is below `2 ^ n` for an instance of length `n`. -/
theorem binaryValue_clockOf_lt (w : List Bool) : binaryValue (clockOf w) < 2 ^ w.length :=
  (binaryValue_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num)
    ((length_dropFrame_le _).trans (length_dropFrame_le _)))

end BoundedHalting

open BoundedHalting

/-- **Bounded halting with a binary time bound**: the bit words `w` such that the machine
described by `descOf w` accepts the input `inputOf w`, i.e. halts with output `[true]`, within the
number of steps written in binary by `clockOf w`. -/
def BoundedHalting : Set (List Bool) :=
  {w | universal (descOf w, (inputOf w).map eBit, binaryValue (clockOf w)) = ([eBit true], true)}

namespace BoundedHalting

theorem mem_iff {w : List Bool} : w ∈ BoundedHalting ↔
    universal (descOf w, (inputOf w).map eBit, binaryValue (clockOf w)) = ([eBit true], true) :=
  Iff.rfl

theorem mk_mem_iff {d : Desc} {x c : List Bool} :
    mk d x c ∈ BoundedHalting ↔ universal (d, x.map eBit, binaryValue c) = ([eBit true], true) := by
  rw [mem_iff, descOf_mk, inputOf_mk, clockOf_mk]

/-- **Bounded halting on descriptions of machines**: the instance for the description of a
binary machine accepts exactly when the machine, run on `x` for `binaryValue c` steps, has halted
with output `[true]`. -/
theorem mk_desc_mem_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x c : List Bool) :
    mk (desc eS eBit tm) x c ∈ BoundedHalting ↔
      (tm.runFrom (tm.initCfg x) (binaryValue c)).Halted ∧
        (tm.runFrom (tm.initCfg x) (binaryValue c)).output = [true] := by
  rw [mk_mem_iff, universal_desc, Prod.mk.injEq, Cfg.Halted, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨hout, hhalt⟩
    exact ⟨hhalt, List.map_injective_iff.mpr eBit.injective (hout.trans List.map_singleton.symm)⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨by rw [hout, List.map_singleton], hhalt⟩

/-- The test with the step bound capped at the unary number `p.2`. -/
private noncomputable def cappedTest (p : List Bool × ℕ) : Bool :=
  decide (universal (descOf p.1, (inputOf p.1).map eBit, boundedBinaryValue p.2 (clockOf p.1)) =
    ([eBit true], true))

private theorem computableInPolyTime_cappedTest :
    ComputableInPolyTime cappedTest (encPair encBits encUnary) encBool := by
  unfold cappedTest descOf inputOf clockOf
  fun_prop

/-- **Bounded halting is in `E`**: the step bound is below `2 ^ |w|`, so capping it there does not
change the answer, and the capped simulation is polynomial in `w` padded with `2 ^ |w|`. -/
theorem mem_E : BoundedHalting ∈ E encBits := by
  convert setOf_mem_E_of_computableInPolyTime_pad computableInPolyTime_cappedTest using 1
  ext w
  simp only [Set.mem_ofPred_eq, cappedTest, decide_eq_true_eq, mem_iff, boundedBinaryValue_eq,
    min_eq_right (binaryValue_clockOf_lt w).le]

/-- **Bounded halting is in `EXP`.** -/
theorem mem_EXP : BoundedHalting ∈ EXP encBits :=
  E_subset_EXP mem_E

/-- **Exponential-time problems reduce to bounded halting.** A problem decided within time
`c₁ * 2 ^ p n + c₂` on instances of encoded length `n`, where `p` is computable in polynomial time
in unary, reduces to bounded halting in polynomial time: `a` maps to the instance that runs the
decider on `enc a` for `2 ^ (p |enc a| + c₁ + c₂ + 1) - 1` steps. -/
theorem polyTimeReducible {α : Type} {enc : α ↪ List Bool} {A : Set α} {p : ℕ → ℕ}
    (hp : ComputableInPolyTime p encUnary encUnary) {c₁ c₂ : ℕ} {s : α → ℕ}
    (hA : DecidableInTimeAndSpace A enc (fun a => c₁ * 2 ^ p (enc a).length + c₂) s) :
    PolyTimeReducible enc encBits A BoundedHalting := by
  obtain ⟨g, ⟨k, State, hfin, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let c := c₁ + c₂ + 1
  refine ⟨fun a => mk (desc eS eBit tm) (enc a) (List.replicate (p (enc a).length + c) true),
    ?_, fun a => ?_⟩
  · have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
    unfold mk
    fun_prop
  · -- the step bound `2 ^ (p n + c) - 1` exceeds the running time `c₁ * 2 ^ p n + c₂`
    have hc : c₁ * 2 ^ p (enc a).length + c₂ ≤
        binaryValue (List.replicate (p (enc a).length + c) true) := by
      have h₁ := binaryValue_replicate_true (p (enc a).length + c)
      have h₂ : 1 ≤ 2 ^ p (enc a).length := Nat.one_le_two_pow
      have h₃ : 2 ^ p (enc a).length * (c₁ + c₂ + 1) ≤ 2 ^ p (enc a).length * 2 ^ c :=
        Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
      have h₄ : c₂ * 1 ≤ c₂ * 2 ^ p (enc a).length := Nat.mul_le_mul_left _ h₂
      rw [pow_add] at h₁
      nlinarith
    obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le hc
    change _ = [g a] at hout
    rw [mk_desc_mem_iff, hg, hout, List.cons.injEq]
    exact ⟨fun h => ⟨hhalt, h, rfl⟩, fun h => h.2.1⟩

/-- **Bounded halting is hard for `E`** under polynomial-time many-one reductions. -/
theorem polyTimeHard_E : PolyTimeHard @E encBits BoundedHalting := fun _ _ _ hA =>
  let ⟨k, _, _, _, hdec⟩ := mem_E_iff.mp hA
  polyTimeReducible (p := fun n => k * n) (by fun_prop) hdec

/-- **Bounded halting is hard for `EXP`** under polynomial-time many-one reductions. -/
theorem polyTimeHard_EXP : PolyTimeHard @EXP encBits BoundedHalting := fun _ _ _ hA =>
  let ⟨k, _, _, _, hdec⟩ := mem_EXP_iff.mp hA
  polyTimeReducible (p := fun n => n ^ k) (by fun_prop) hdec

/-- **Bounded halting with a binary time bound is `E`-complete** under polynomial-time many-one
reductions. -/
theorem polyTimeComplete_E : PolyTimeComplete @E encBits BoundedHalting :=
  ⟨mem_E, polyTimeHard_E⟩

/-- **Bounded halting with a binary time bound is `EXP`-complete** under polynomial-time many-one
reductions. -/
theorem polyTimeComplete_EXP : PolyTimeComplete @EXP encBits BoundedHalting :=
  ⟨mem_EXP, polyTimeHard_EXP⟩

/-- **Bounded halting is not in `P`**: otherwise every problem in `EXP` would be, contradicting
`P ⊊ EXP`. -/
theorem notMem_P : BoundedHalting ∉ P encBits := fun h =>
  let ⟨_, hA, hAP⟩ := Set.exists_of_ssubset P_ssubset_EXP
  hAP ((polyTimeHard_EXP encBits _ hA).mem_P h)

end BoundedHalting

end Cslib.Complexity
