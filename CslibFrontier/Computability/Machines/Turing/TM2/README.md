# Mathlib stack machines and multi-tape machines

Import `CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer` for both directions.

`Turing.MultiTapeTM.computableInPolyTime_iff_tm2` identifies polynomial-time computation
with the existence of a Mathlib `TM2ComputableInPolyTime` certificate whose **every** stack
alphabet is finite. `Cslib.Complexity.mem_PSPACE_iff_tm2` identifies `PSPACE` with terminating
Boolean TM2 computation whose reachable stacks are polynomially bounded. The space result has
no runtime assumption. Both use the original binary input/output encodings.

For plain source machines, use
`ComputableInTimeAndSpace.exists_tm2ComputableInPolyTime` or
`ComputableInTimeAndSpace.exists_tm2Computable_bool`. The general
`ComputableInTimeAndSpace.exists_tm2Computable` also asks for polynomial output length.
`ComputableInPolySpace` already includes polynomial output length and therefore admits the
function equivalence `computableInPolySpace_iff_tm2`.

The direct compiler is `Turing.MultiTapeTM.ToTM2.machine q₀ transition`. Its input and output
alphabets are `Bool`; work-stack alphabets are `Option Bool`. Each source work tape uses two
stacks and a current cell in finite control. The read-only input uses two binary stacks and a
boundary flag. Output is accumulated in reverse order. Cleanup clears auxiliaries, reverses
the output and restores Mathlib's complete canonical `haltList`.

For a fixed source machine with `k` work tapes, input length `n`, source runtime bound `t`,
work-space bound `s` and output length `o`, `ToTM2.outputsInTime` proves a target clock of
`n + (k + 1) * (t + 1) + o + 3`. `ToTM2.reachable_stack_bound` proves **total** stack length
at most `n + s + o` at every target step, including initialization, cleanup and padding after
halting. The space bound is independent of runtime; output length is at most source runtime.

The existing forward simulation gives polynomial overhead. It uses framed finite-symbol word
encodings; `TM2.Recoding` removes this recoding by conversions on words, without a computable
inverse for either typed embedding. TM2 stores its input, whereas native work space excludes
read-only input and write-only output. Consequently these equivalences do not identify
sublinear space bounds, nor claim linear space overhead in the forward direction.
