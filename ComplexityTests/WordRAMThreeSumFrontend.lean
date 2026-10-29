/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

meta import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Program

/-!
# Executed initialized-input frontend boundary cases

These checks execute the complete structured native program, including parameters and radix.
The observation follows each concrete descriptor and decodes its compact payload to a set.
-/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ThreeSum.Frontend

private meta def observe (κ w : ℕ) (input : List ℤ) :
    Option (List (Finset ℤ × Finset ℤ × Finset ℤ) × ℕ) :=
  ((program κ).eval w 512 (Data.init (input.map Signed.encode))).map fun (x, time) =>
    let array (a : ℕ) := ((List.range (x.mem a)).map fun i =>
      Signed.decode (x.mem (x.mem (a + 1) + i))).toFinset
    ((List.range (x.regs descriptorCount)).map fun i =>
      let a := x.regs descriptorBase + 6 * i
      (array a, array (a + 2), array (a + 4)), time)

private meta def exact (κ : ℕ) (input : List ℤ) : Bool :=
  (observe κ 64 input).map (fun p => p.1 == Cslib.Algorithms.ThreeSum.inputs
    ((input.length + 2) ^ κ) (fun i : Fin input.length => input[i])) == some true

-- Empty arrays coexist with all constant singleton-zero arrays; exponent zero is admitted.
/-- info: true -/
#guard_msgs in
#eval exact 0 []

-- One and two positions are kept exactly; signed endpoints remain canonical.
/-- info: true -/
#guard_msgs in
#eval exact 0 [-1]

/-- info: true -/
#guard_msgs in
#eval exact 1 [-4, 4]

-- Nonzero multiplicity one versus two; twiceSet uses positive 2*a.
/-- info: true -/
#guard_msgs in
#eval exact 1 [1, -2]

/-- info: true -/
#guard_msgs in
#eval exact 1 [1, 1, -2]

-- Zero multiplicity two versus three, and full multiplicity above three.
/-- info: true -/
#guard_msgs in
#eval exact 0 [0, 0]

/-- info: true -/
#guard_msgs in
#eval exact 0 [0, 0, 0]

/-- info: true -/
#guard_msgs in
#eval exact 0 [0, 0, 0, 0, -1, -1, 1]

-- Actual distinct-position yes/no inputs, including three distinct values and equal bit positions.
/-- info: true -/
#guard_msgs in
#eval exact 1 [-3, 1, 2]

/-- info: true -/
#guard_msgs in
#eval exact 1 [1, 2, 3]

-- Two successful physical widths give identical output and charged time.
-- Both are below the exported sufficient threshold of 1692 for this input.
/-- info: true -/
#guard_msgs in
#eval decide (observe 1 64 [-3, 1, 2] = observe 1 512 [-3, 1, 2])

-- Invalid width faults during genuine setup/layout arithmetic.
/-- info: true -/
#guard_msgs in
#eval decide (observe 0 3 [] = none)
