/-
Copyright (c) 2026 Bolton Bailey, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines

/-!
# Executable compact configuration graphs

A fixed finite-state binary nondeterministic multi-tape machine has a compact configuration graph
for every radix `B`: each vertex packs, below `B`, an input position, control tag, output summary
and two ternary stacks plus a head per work tape. The original input word is omitted. When every
reachable view fits the radix, the graph is exact; a machine using logarithmic work space fits the
radix `(n+2)^D` for a fixed `D`, so its graph has polynomially many natural-number vertices. A
vertex *overflows* when one of its steps leaves the radix; a graph in which no reachable vertex
overflows already represents every reachable view, whatever the space of the machine.

The local edge routine uses one supplied input symbol, forces blank at the native boundary cells,
and otherwise performs deterministic arithmetic in linear workspace in the binary radix, length
and vertex IDs. Its `ComputableInSpace` certificate is for an actual native multi-tape
machine. The graph-to-source correctness theorem applies without a source halting assumption.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.startID`: initial vertex.
* `Turing.MultiTapeNTM.ConfigurationGraph.queryIndex`: the sole requested input-bit position.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol`: local guarded edge query.
* `Turing.MultiTapeNTM.ConfigurationGraph.bad`: accepting halted vertices.
* `Turing.MultiTapeNTM.ConfigurationGraph.overflow`: vertices with a step leaving the radix.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad`: exact graph of a radix
  fitting every reachable view.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_of_not_overflow`: no reachable overflow means
  every reachable view fits.
* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace`: exact graph
  in logarithmic space.
* `Turing.MultiTapeNTM.ConfigurationGraph.vertexID_lt_pow_of_runsInSpace`: polynomial ID bound.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_budget`: native local edge routine.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/
