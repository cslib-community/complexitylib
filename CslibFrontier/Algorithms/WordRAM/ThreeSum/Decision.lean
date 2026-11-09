/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Intermediates
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Host.Slow

/-!
# Native ordinary 3SUM with an in-place Chan–He visitor

`Decision.runs_input` starts from signed-encoded `State.init` input, computes the frontend and
consumes each actual packed Chan–He node through the certified Convolution host before pushing its
children. It follows the exact finite preorder, including multiplicity, and does not stop after a
positive call. The raw Boolean decides whether three distinct original input positions sum to
zero; equal values at different positions are permitted.

For each fixed magnitude exponent and concrete certified Exact Triangle block, one finite
standard-basis program has a register count independent of length and physical width.
`Host.Callee` supplies actual code with an explicit matrix, width, frame and time contract.
`Host.Slow.callee` gives a finite exhaustive instance of that protocol.

Each call receives the current node's actual packed pointer and allocation endpoint. Its return
frame preserves the lower prefix, including pending heavy arrays, while higher scratch may be
dirty. The ordinary path neither publishes nor reads a packed-pointer table. One native copy then
releases the packed, residue and histogram tail for later construction. Persistent heavy-buffer
capacities and count cells remain allocated, and their frontier advances monotonically with the
old table gap reserved. No improved total-space or callee high-water bound is asserted. The
standalone catalogue-producing preprocessing API remains available independently.

`Decision.width` and `Decision.cost` retain their existing values. Initialized execution and every
reachable prefix at every admitted wider width retain the polynomial word and zero-support bounds.
The concrete 848-register endpoint in `ThreeSum.Decision.One9992` supplies ordinary native time
O(n^1.9992); import that module for the final theorem. Curated selection is separate.

## Main definitions

* `Decision.program`, `Decision.flatProgram`: the canonical fixed visitor and raw Boolean halt.
* `Host.Callee`, `Host.Slow.callee`: the actual solver protocol and exhaustive instance.
* `Decision.cost`, `Decision.width`: shared charged time and physical-width envelopes.

## Main results

* `Decision.exec_input`, `Decision.runs_input`: initialized execution and exact verdict.
* `Decision.prefix_polynomial`: word magnitudes and memory support at every admitted prefix.

The finite reduction and Convolution builder retain their Anthropic source credit. The native
visitor, caller-owned layout, ordinary composition and exhaustive callee are original.
-/
