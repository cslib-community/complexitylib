/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORCompactExecution
import all Complexity.Cryptanalysis.AddXNORUniformExecution
import all Complexity.Cryptanalysis.AddXNORDissection
import all Complexity.Cryptanalysis.AddXNORGeneratedRunInput
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Submission 733's original operand convention and consecutive quarter cut

The input is unary width/requested projection depth and one binary operand list.
The machine computes `q = N - 1`, `k = q / 4`, uses the first operand as seed and
zero as target, and splits the remaining operands into consecutive lengths
`k,k,k,q-3*k`. No seed, target, quarter lengths or prepartitioned arrays are advice.
Projection depth is capped at both physical width and `k`, explicitly covering
all remainders and small inputs. On the source's admitted depths this cap is inert.

The actual preprocessing certificate composes with the compacting uniform execution
machine. This supplies source-convention correctness, not sharp bit resource
asymptotics. Input validation outside the typed bit-word image is not asserted.
Source: [WangLvShenZhang2027], PDF Section 5 (p. 20), Lemma 8/Theorem 7 (pp. 21–22).
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.Source
open Turing.MultiTapeTM Cslib.GenericRAM Cslib.WordRAM
open ProgramGeneration GeneratedRunInput Native.Driver

/-- Unary physical width/requested class depth and the original-order binary operand list. -/
abbrev Input := (ℕ × ℕ) × List ℕ

/-- Every original operand, including its seed, is charged on the input tape. -/
def encoding : Input ↪ List Bool := encPair (encPair encUnary encUnary) (encList encNat)

/-- The paper's consecutive quarter cut; the fourth part keeps the full remainder. -/
def quarters {α : Type} (xs : List α) : (List α × List α) × (List α × List α) :=
  let k := xs.length / 4
  ((xs.take k, (xs.drop k).take k),
    ((xs.drop k |>.drop k).take k, xs.drop k |>.drop k |>.drop k))

/-- The actual quarter cut neither reorders nor loses operands. -/
theorem quarters_append {α : Type} (xs : List α) :
    ((quarters xs).1.1 ++ (quarters xs).1.2) ++
      ((quarters xs).2.1 ++ (quarters xs).2.2) = xs :=
  Dissection.four_quarters xs (xs.length / 4)

/-- The three complete quarters have length `k`; the last includes all residue cases. -/
theorem quarters_lengths {α : Type} (xs : List α) :
    let k := xs.length / 4
    (quarters xs).1.1.length = k ∧ (quarters xs).1.2.length = k ∧
      (quarters xs).2.1.length = k ∧ (quarters xs).2.2.length = xs.length - 3 * k := by
  have h := Nat.div_mul_le_self xs.length 4
  simp only [quarters, List.length_take, List.length_drop]
  omega

/-- All quarter splitting, first-operand selection, class-depth capping and zero target are
computed from the original runtime input, with no supplied semantic parameters. -/
def prepare (x : Input) : ProgramGeneration.Source :=
  let tail := x.2.tail
  let parts := quarters tail
  (((x.1.1, min x.1.2 (min x.1.1 (tail.length / 4))), (x.2.headD 0, 0)), parts)

/-- The complete source-to-packet-input materialization is uniformly polynomial in bit size. -/
theorem prepare_polyTime : ComputableInPolyTime prepare encoding sourceEncoding := by
  have tail : ComputableTidilyInPolyTime (fun x : Input => x.2.tail)
      encoding (encList encNat) := by fun_prop
  have k : ComputableTidilyInPolyTime (fun x : Input => x.2.tail.length / 4)
      encoding encUnary := by fun_prop
  have m : ComputableTidilyInPolyTime (fun x : Input => x.1.1)
      encoding encUnary := by fun_prop
  have p : ComputableTidilyInPolyTime (fun x : Input => x.1.2)
      encoding encUnary := by fun_prop
  have depth := ComputableTidilyInPolyTime.unary_min.comp
    (p.prod (ComputableTidilyInPolyTime.unary_min.comp (m.prod k)))
  have d1 := (ComputableTidilyInPolyTime.dropUnary (encA := encNat)).comp (tail.prod k)
  have d2 := (ComputableTidilyInPolyTime.dropUnary (encA := encNat)).comp (d1.prod k)
  have d3 := (ComputableTidilyInPolyTime.dropUnary (encA := encNat)).comp (d2.prod k)
  have q1 := (ComputableTidilyInPolyTime.takeUnary encNat).comp (tail.prod k)
  have q2 := (ComputableTidilyInPolyTime.takeUnary encNat).comp (d1.prod k)
  have q3 := (ComputableTidilyInPolyTime.takeUnary encNat).comp (d2.prod k)
  have seed : ComputableTidilyInPolyTime (fun x : Input => x.2.headD 0)
      encoding encNat := by fun_prop
  have c := (m.prod depth).prod (seed.prod (ComputableTidilyInPolyTime.const (encMid := encNat) 0))
  apply ComputableInPolyTime.of_tidy
  apply (c.prod ((q1.prod q2).prod (q3.prod d3))).of_enc_eq
  intro x
  rfl

/-- Actual preparation machine, charging all intermediate lists, headers and operands. -/
noncomputable def prepareCertificate : NativeCertificate prepare encoding sourceEncoding :=
  .ofPolyTime prepare_polyTime

/-- Typed original words provide no separate executable, seed or quarter metadata. -/
def ofWords {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) : Input :=
  ((m, p), (a :: tail).map BitVec.toNat)

/-- Source calling convention agrees exactly with the existing original-input packet pipeline. -/
theorem prepare_ofWords {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    prepare (ofWords p a tail) =
      originalSource (min p (min m (tail.length / 4)))
        (quarters tail).1.1 (quarters tail).1.2 (quarters tail).2.1 (quarters tail).2.2 a 0 := by
  simp [prepare, ofWords, quarters, originalSource, BitInput.words,
    List.map_take, List.map_drop]

/-- On the source's admitted class depths, both explicit projection caps are inert. -/
theorem prepare_ofWords_admitted {m p : ℕ} (hm : p ≤ m)
    (a : BitVec m) (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) :
    prepare (ofWords p a tail) = originalSource p
      (quarters tail).1.1 (quarters tail).1.2 (quarters tail).2.1 (quarters tail).2.2 a 0 := by
  rw [prepare_ofWords, Nat.min_eq_left (le_min hm hk)]

/-- One machine now receives the original single operand list and computes its own source ABI. -/
noncomputable def sourceCertificate : NativeCertificate
    ((GeneratedRunInput.run ∘ packet) ∘ prepare) encoding encBits :=
  CompactExecution.sourceCertificate.comp prepareCertificate

/-- Source correctness from the first operand and zero target, for every quarter residue.
Malformed/empty raw lists are outside this typed nonempty-source theorem. -/
theorem original_correct {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    ∃ out : Option (List Bool),
      GeneratedRunInput.run (packet (prepare (ofWords p a tail))) = encOption encBits out ∧
      (out = none ↔ ¬Solvable tail a 0) ∧
      (∀ ops, out = Option.some ops → ops.length = tail.length ∧ eval (ops.zip tail) a = 0) := by
  rw [prepare_ofWords]
  obtain ⟨out, result, miss, sound⟩ := GeneratedRunInput.original_correct
    (p := min p (min m (tail.length / 4))) (by omega)
    (quarters tail).1.1 (quarters tail).1.2 (quarters tail).2.1 (quarters tail).2.2 a 0
  refine ⟨out, result, ?_, ?_⟩
  · simpa only [quarters_append] using miss
  · intro ops hops
    have hs := sound ops hops
    have hlen := congrArg List.length (quarters_append tail)
    simp only [List.length_append] at hlen
    exact ⟨by dsimp only [totalLength] at hs; omega,
      by simpa only [quarters_append] using hs.2⟩

/-- One finite-control multitape machine executes all source-convention instances, including
computed splitting/seed/zero target and compacted simulated prefixes. Bounds retain actual
scanning/workspace overhead and do not assert the paper's sharp asymptotics. -/
theorem original_machine : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q)
    (machine : Turing.MultiTapeTM k Bool Q),
    ∀ (m p : ℕ) (a : BitVec m) (tail : List (BitVec m)), ∃ out : Option (List Bool),
      machine.ComputesInTimeAndSpace (encoding (ofWords p a tail)) (encOption encBits out)
        (c * (sourceCertificate.time (ofWords p a tail) + 1))
        (c * (sourceCertificate.space (ofWords p a tail) + 1)) ∧
      (out = none ↔ ¬Solvable tail a 0) ∧
      (∀ ops, out = Option.some ops → ops.length = tail.length ∧ eval (ops.zip tail) a = 0) := by
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := sourceCertificate.computes
  refine ⟨c, k, Q, hQ, machine, fun m p a tail => ?_⟩
  obtain ⟨out, result, miss, sound⟩ := original_correct p a tail
  refine ⟨out, ?_, miss, sound⟩
  simpa only [encBits_apply, Function.comp_apply, result] using computes (ofWords p a tail)

/-- The actual prepared runtime packet's compacted-prefix maximum is bounded by the derived
native peak allowance, including zero target, first-operand seed and computed consecutive
quarter lengths. Interpreter workspace/scan overhead is still separate. -/
theorem compact_trajectory_bound {m : ℕ} (p : ℕ) (a : BitVec m)
    (tail : List (BitVec m)) :
    let parts := quarters tail
    let depth := min p (min m (tail.length / 4))
    let x := GeneratedRunInput.packet (prepare (ofWords p a tail))
    Interpreter.compactTrajectoryLength (UniformExecution.executionInput x) ≤
      2 * (Interpreter.parametersEncoding 40 ((UniformExecution.executionInput x).2.1)).length +
        1 + stateBound 40 (labelBound x.1.1.parkHalts.toGeneric) x.1.2.1
          (CompactExecution.peak depth parts.1.1.length parts.1.2.length
            parts.2.1.length parts.2.2.length
            (computedBalance (p := depth) parts.1.1 parts.1.2 parts.2.1 parts.2.2 a 0)) := by
  dsimp only
  rw [prepare_ofWords, GeneratedRunInput.packet_original]
  dsimp only [UniformExecution.executionInput]
  exact CompactExecution.original_compact_trajectory (p := min p (min m (tail.length / 4)))
    (by omega) (quarters tail).1.1 (quarters tail).1.2 (quarters tail).2.1 (quarters tail).2.2 a 0 _

end Cslib.Cryptanalysis.AddXNOR.Source
