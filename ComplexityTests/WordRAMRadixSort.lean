import Complexity.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM

private def observe (w fuel : ℕ) (xs : List ℕ) : Option (List ℕ × List ℕ × ℕ) :=
  (Code.eval w fuel RadixSort.inputCode (Data.init xs)).map fun (y, _) =>
    let m := y.regs Deduplicate.out
    ((List.range m).map (fun i => y.mem (1 + 2 * xs.length + i)),
      (List.range m).map (fun i => y.mem (1 + 3 * xs.length + i)), m)

-- Empty input still executes setup and exits both array scans safely.
/-- info: true -/
#guard_msgs in
#eval decide (observe 3 4 [] = some ([], [], 0))

-- The largest fitting four-bit canonical signed encoding occurs at the key boundary.
/-- info: true -/
#guard_msgs in
#eval decide (observe 4 5 [Signed.encode (-7)] = some ([15], [1], 1))

-- Zero is canonical; a repeated zero is one key with full multiplicity two.
/-- info: true -/
#guard_msgs in
#eval decide (observe 4 5 [0, 0] = some ([0], [2], 1))

-- Counts are full multiplicities, including values above three.
/-- info: true -/
#guard_msgs in
#eval decide (observe 5 6 (List.replicate 4 (Signed.encode (-1))) = some ([3], [4], 1))

-- Positive and negative input integers, repeated keys, and zero in unsigned encoding order.
/-- info: true -/
#guard_msgs in
#eval decide (observe 5 6 (([2, -1, 2, 0, -1] : List ℤ).map Signed.encode) =
  some ([0, 3, 4], [1, 2, 2], 3))

-- Encoding order deliberately differs from signed integer order.
/-- info: true -/
#guard_msgs in
#eval decide (observe 4 5 (([-2, 1, -1] : List ℤ).map Signed.encode) =
  some ([2, 3, 5], [1, 1, 1], 3))

-- Two physical bits cannot address this singleton's count output: layout fit matters.
/-- info: true -/
#guard_msgs in
#eval decide (observe 2 4 [2] = none)

-- Key overflow faults even when the singleton's four-buffer layout fits.
/-- info: true -/
#guard_msgs in
#eval decide (observe 4 5 [16] = none)

-- The assembled program is executed using the ordinary native initial state.
/-- info: true -/
#guard_msgs in
#eval decide ((run 4 RadixSort.program 500 (State.init [4, 3, 3])).map Prod.fst = some 2)

-- The array layout threshold includes zero and small input lengths.
example : RadixSort.layoutWidth 0 = 3 ∧ RadixSort.layoutWidth 2 = 6 := by decide +kernel

-- A bit bound of zero is meaningful exactly when all unsigned keys are zero.
example : RadixSort.passes 0 [0, 0] = [0, 0] ∧
    ¬([2, 0] : List ℕ).Pairwise (· ≤ ·) := by decide +kernel

-- One finite instruction list is used at every input length and word width.
example : RadixSort.program.length = 81 := by decide +kernel
