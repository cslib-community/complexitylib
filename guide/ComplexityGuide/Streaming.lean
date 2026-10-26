/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Complexity.Algorithms.Streaming.CountMin.LinearHash
import Complexity.Algorithms.Streaming.CountMin.Program

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "Streaming and Sketching" =>
%%%
tag := "streaming-and-sketching"
%%%

A frequency sketch processes updates while keeping a table of counters. A query estimates how
much weight an item has received. Count-Min provides a useful first example: its estimate is
always at least the true frequency, and independently sampled hash rows bound the probability
of a large overestimate.

This chapter uses weighted insertions. An event `(x, c)` adds the natural number `c` to item `x`;
the stream is a `List (X × ℕ)`. The list describes the input to the correctness theorem. The
stored table contains only counters, and {name}`Cslib.CountMin.update` can process one new event
from the current table.

```
import Complexity.Algorithms.Streaming.CountMin.LinearHash
import Complexity.Algorithms.Streaming.CountMin.Program

open Cslib.CountMin
```

```lean -show
open Cslib.CountMin
```

# Updates and Queries
%%%
tag := "count-min-updates"
%%%

{name}`Cslib.CountMin.Table` `d w` is a vector of `d` rows, each with `w` natural-number counters.
A hash bank `h : Fin d → X → Fin w` selects one bucket per row for each item. An update adds its
weight to those buckets. {name}`Cslib.CountMin.run` folds the update function over the stream,
starting from zero. A query takes the minimum of its addressed counters, so queries require
at least one row.

Here two rows hash the low and high bits of four possible items. Item `3` is absent from the
stream, and the other three items have different weights.

```lean
def exampleHash (r : Fin 2) (x : Fin 4) : Fin 2 :=
  if r = 0 then ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
  else ⟨x.val / 2, by omega⟩

def exampleStream : List (Fin 4 × ℕ) := [(0, 2), (1, 3), (2, 5)]

example : (run exampleHash exampleStream).toList.map Vector.toList =
    [[7, 3], [5, 5]] := by
  decide

example : List.ofFn (fun x : Fin 4 =>
    estimate exampleHash (run exampleHash exampleStream) x) =
      [5, 3, 5, 3] := by
  decide
```

The true frequencies are `2, 3, 5, 0`. Collisions increase the estimates for items `0` and `3`.
An absent item can therefore have a positive estimate. The deterministic guarantee is
{name}`Cslib.CountMin.frequency_le_estimate_run`:

```lean
example (x : Fin 4) : frequency exampleStream x ≤
    estimate exampleHash (run exampleHash exampleStream) x :=
  frequency_le_estimate_run exampleHash exampleStream x
```

# Merging Streams
%%%
tag := "count-min-merging"
%%%

Tables computed with the same hash bank merge by adding corresponding counters.
{name}`Cslib.CountMin.run_append` identifies this operation with processing the concatenated
streams. The equality concerns the whole table; taking minima does not make point estimates
additive.

```lean
example : merge (run exampleHash [(0, 2)])
    (run exampleHash [(1, 3), (2, 5)]) = run exampleHash exampleStream := by
  decide
```

For online processing, {name}`Cslib.CountMin.run_append_singleton` identifies appending one
event to the input with applying one update to the current table.

# Randomness and Accuracy
%%%
tag := "count-min-accuracy"
%%%

The random choice is a seed for each hash row. A two-universal family bounds the collision
probability of any two distinct items by the reciprocal of the number of buckets. Count-Min
needs independent row seeds as well: the guarantee samples a uniform tuple of seeds, rather
than reusing one seed across all rows.

For a stream and query fixed before sampling, let `M` be {name}`Cslib.CountMin.mass` of the
stream and let `f` be the queried frequency. The theorem
{name}`Cslib.CountMin.dens_estimate_error_le` bounds the probability that the estimate exceeds
`f + ε * M` by `(w * ε)⁻¹ ^ d`, for positive `ε`, `w`, and `d`.
{name}`Cslib.CountMin.dens_estimate_error_le_inv_two_pow` specializes this to `2⁻ᵈ` when
`2 ≤ w * ε`. With four buckets, three rows, and `ε = 1/2`, the bound is `1/8`.
Zero total weight is included and gives an identically zero table.

The concrete family {name}`Cslib.CountMin.indexedHash` hashes `n`-bit items to `2^m` buckets
using a binary matrix with `m` rows. Its collision guarantee is
{name}`Cslib.CountMin.isTwoUniversal_indexedHash`. Each row of the sketch needs a separate
matrix seed with `m * n` bits.

{name}`Cslib.CountMin.sampleSketch` is a `ProbComp` program that calls a supplied seed sampler
independently for each row, then processes the stream. Its result stores the seeds and counter
table; later queries must use the same hash family. The evaluation theorem assumes that one
call to the sampler is exactly uniform. {name}`Cslib.CountMin.sampleQuery` constructs a sketch
and returns one fixed query, and {name}`Cslib.CountMin.sampleQuery_error_le_inv_two_pow`
proves the same failure bound for the actual program's output law.

These results formalize Count-Min's insertion-only point-query guarantee from
[Cormode and Muthukrishnan, Section 4.1, Theorem 1][count-min]. They do not cover adaptive
updates or queries, deletions, or heavy-hitter enumeration. The table has `d * w` counters,
each at most `M`, but machine time and bit-space certificates, including the hash seeds, remain
separate work. The [checked examples][examples] include concrete collisions, merging, zero
weights, and a universal-hash accuracy instance.

[count-min]: https://www.cs.ox.ac.uk/people/graham.cormode/pubs/papers/cm-full.pdf
[examples]: https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/CountMin.lean
