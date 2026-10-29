/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Intermediates
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Slow

/-!
# Native ordinary 3SUM host with a concrete finite Exact Triangle callee

`Decision.runs_input` starts with actual signed-encoded `State.init` input, executes complete
Chan–He preprocessing, reads its raw output table/count/common length, and invokes a caller-safe
native Convolution host for every actual payload. It returns the existing integer 3SUM verdict:
three distinct input positions summing to zero, with equal values permitted.

For each fixed magnitude exponent and concrete certified finite Exact Triangle block, there is
one finite standard-basis program with a fixed register count independent of input length and
physical width. The actual callee code must meet `Host.Callee`'s explicit matrix/width/frame/time
contract on arbitrary old scratch memory. `Host.Slow.callee` proves that this contract is inhabited
by a finite exhaustive native program, without a solver oracle.

The positive threshold `Decision.width` is logarithmic in the original input length; it derives
all intermediate and address fits. Every prefix at every wider admitted width has polynomial
word magnitudes and memory support. `Decision.cost` charges preprocessing, every catalogue and
loop operation, every matrix builder and every callee instruction at the actual packed size.

This conditional host is not a fast Exact Triangle solver. The unconditional truly subquadratic
native 3SUM algorithm, its final asymptotic composition and published exponent 1.9992 remain open.
No curated headline changes here.

## Main definitions

This import-only module re-exports these definitions:

* `Decision.flatProgram`: one actual finite ordinary 3SUM host per exponent and callee.
* `Host.Callee`: explicit actual finite-code protocol and certification requirements.
* `Host.Slow.callee`: fully proved finite exhaustive native Exact Triangle instance.
* `Decision.cost`, `Decision.width`: compositional charged time and global physical width.

## Main results

It also re-exports these results:

* `Decision.exec_input`, `Decision.runs_input`: exact initialized native verdict and real run.
* `Decision.intermediates_polynomial`, `Decision.space_polynomial`: every-wide-prefix bounds.

The finite mathematical reduction and underlying Convolution builder retain their existing
Anthropic source credit. The caller-owned layout, ordinary native composition and exhaustive
callee are original.
-/
