# Complexitylib Agent Operator's Manual

This short manual is for people directing agents in Complexitylib. It explains whom to ask,
what to ask for, and how to judge the handoff. The substantial [Operator's Manual](README.md)
explains how to work in the codebase: its tactics, models, proof patterns, examples and procedures.
Both humans and agents use that reference. You do not need an agent to follow it.

The current [project instructions](../AGENTS.md) and [contribution policy](../CONTRIBUTING.md)
govern the work. This manual explains how to use that process; it does not grant an agent
permission to merge, publish, or change another contributor's work.

## Choose the right assignment

An agent can investigate, implement, coordinate or review. State the assignment when starting
a session; the repository defaults an unspecified agent to **worker**.

| Assignment | What the agent does | What you should expect |
|---|---|---|
| Worker | Owns a bounded task, implements it on a branch, checks clients and documentation, and hands it over for review | A concrete change, actual validation results and a clear remaining gap, if any |
| Coordinator | Reviews submitted work, resolves ownership and dependencies, arranges independent review, and manages integration when authorized | A current account of what is ready, what is blocked and what actually landed |
| Independent reviewer | Inspects a change without having designed or implemented it | Specific findings or an approval of an identified revision, with the scope and limits of the review |

Reviewer is a review assignment, not an exemption from the worker/coordinator rules. An author
cannot become independent by changing their role name. Agents using the same account can be
independent reviewers, but an agent verdict is not human or platform approval.

Use a worker for one proof, API improvement or bounded investigation. Use a coordinator when
several tasks or PRs need sequencing, review and integration. Identify the coordinator responsible
for that scope so several sessions do not independently take over the same queue.

## Give the agent a useful starting point

Give the intended result, the issue or PR if one exists, the relevant checkout, and any important
constraints. For mathematics, specify the intended model and strength of the result. State merge
or publication authority explicitly when you want those actions. The agent should read the current
instructions, check ownership and existing work, and use the appropriate branch or worktree.

A bounded implementation request can be as simple as:

> Act as a worker on issue `<number>`. Read the current project instructions and inspect existing
> work first. Implement `<concrete result>` with a representative checked client. Preserve the
> intended model and hypotheses; report a narrower milestone as such. Update the affected
> Operator's Manual sections and assess the Agent Operator's Manual. Validate the change and
> prepare it for independent review.

For an investigation, ask for a decision you can use:

> Inspect how `<task>` is currently expressed in the library. Show the relevant definitions and a
> complete existing client, identify the main difficulty, and propose a bounded next step. State
> which conclusions come from source inspection and which were checked by running Lean.

For orientation, it is useful to ask an agent to summarize `AGENTS.md` for its assigned role and
point to the relevant manual sections. Require source locations for substantive claims. The
manuals provide a shared reference when a summary omits something or two agents disagree.

## Read a progress report

Ask for the result and the next decision, rather than a transcript of every tool call. A useful
report distinguishes these states:

| State | Meaning and useful next step |
|---|---|
| Active | A named agent owns the task; ask what has been established and what remains |
| Blocked | Progress needs a specific input or external change; ask for the exact obstacle and options |
| Awaiting review | Implementation has been handed off; keep the owner and arrange review |
| Changes requested | A reviewer found something to resolve; ask for the fix and review of the affected delta |
| Queued | Integration is pending; the coordinator should follow the queue through to a result |
| Landed | The change reached the target branch; check whether the broader objective is also complete |

A statement, its proof, a usable API, successful validation and completed integration are different
deliverables. For a mathematical milestone, ask what remains unproved. For a failed build, ask
which command failed and whether it was a proof failure, a resource problem or an environment
failure. The [codebase troubleshooting chapter](workflows/troubleshooting.md) explains the layers.

## Ask for review that answers the real question

Assign review to an agent that did not design or implement the change. For example:

> Independently review PR `<number>` at its current revision. Read the actual definitions and
> statements. Check the mathematical claim, API and representative client, including the model,
> encodings, hypotheses and resource bounds. Review the impact on both manuals and any affected
> formal abstract. Report concrete findings and a verdict, stating what you checked and what
> remains uncertain.

Lean validation establishes the checked statements under their definitions and dependencies.
Review must also judge whether those statements express the intended mathematics and whether
someone can use the interface. Ask for a satisfying instance or meaningful edge case when a
contract may be vacuous. An approval must cover the final revision; substantive fixes require
review of the affected reasoning. Unchanged evidence can be reused after checking its identity.

## Direct a coordinator

Make the scope and authority clear. A coordinator request can say:

> Coordinate `<issues or PRs>`. Inspect current ownership and existing reviews before assigning
> work. Prioritize reviewing and landing ready changes over starting more tasks. Check both
> manuals as part of every review, including any justified no-impact assessment. Arrange
> non-author review for your own changes. Report what landed, remaining objectives and blockers.

Reviewers with write access queue the exact heads they approve, so an approved PR does not wait for
a coordinator ([Approve and queue](../AGENTS.md#approve-and-queue)). To keep a PR for your own
review, say so in the PR or its linked issue: agents then approve it without queueing, and you or
someone you name queues it. Agents without write access can prepare and review work but cannot
queue it. Coordinators queue approved heads still waiting and monitor the merge queue through
landing. [Coordinator duties](../AGENTS.md#coordinators) define the details.
When the queue ejects a PR whose only conflict is in `references.bib`, the coordinator or author
can run `python3 scripts/resolve_bib_conflict.py origin/<branch>` after `git fetch origin` to
write the merge with `main` instead of sending the PR back. It refuses any other conflict and
pushes nothing. Pushing its commit to the PR branch is a deliberate step by the author or a
coordinator acting for them, who records the push. Existing approval carries forward when
`scripts/check_restack.py` passes and CI passes at the new head, as
[Restacks](../AGENTS.md#restacks) describes.

The manuals are part of this workflow. Changes to library usage belong in the Operator's Manual;
changes to roles, delegation, review or human direction may affect this Agent Operator's Manual.
Coordinators check both against the final change. A reasoned finding of no impact is valid;
an unchecked box or a passing build is not a usability review. When reviewing
resource results, inspect what is counted: a simultaneous bound at every actual
execution prefix, total historical allocation and a class-average estimate have
different meanings. Preserve the stated machine model when reporting a milestone;
a native RAM word bound alone does not supply a multitape bit-time theorem. A separately proved
bit codec also needs a charged connection to its producing machine; an already
serialized codec input is a material calling convention, not a full simulation.
A concrete fixed-program simulator may charge input conversion and memory extraction
while its machine and constants still depend on scalar parameters. Check whether
programs/headers are runtime encoded inputs or fixed parameters, and keep sparse
stored bindings distinct from live nonzero support before transferring resource bounds.
A uniform code/width/clock/input-state generator does not itself supply one bit machine
that dispatches the generated program at runtime. Ask for both the generation certificate
and the runtime execution certificate before reporting a uniform algorithm.
For example, `AddXNORUniformExecution.original_machine` quantifies one machine before
all original inputs; `Interpreter.clocked_resources` charges its full encoded
prefix trajectory and binary clock. Its uniformity proof does not turn native live
support into a bound on retained sparse zero bindings or supply source sorted-list
asymptotics. The separate compacting implementation now really deletes those
bindings and derives a prefix encoding bound; that still does not bound internal
interpreter/scan workspace sharply. Check the executed normalization and transient
workspace, not just the retained wire. `AddXNORSource` computes the source's single
operand list cut, seed and zero target, with explicit projection caps. Keep sharp
bit time/peak space and the other remaining objectives visible in handoffs. The separate
`RadixSort.computable` now certifies uniform streaming radix sorting with time
linear in materialized record count times polynomial width overhead and peak
space charging complete lists and per-record buffers. Its source record bridge
preserves packed witnesses and collisions, but does not charge generation,
counting, class access or reuse. The alternative streaming compactor is not wired
into `CompactExecution`; preserve that path's cubic filter charge. A sorted-list
component is progress toward the source model, not its global resource theorem.
`SourceQuarter.run`
now composes actual original-input preparation, projected first-quarter generation,
packed-chain evaluation and sorting. Its quarter time/peak-space certificate
charges every generated prefix and bit-machine temporary. It supplies a sharp
quarter component, not full class enumeration or a whole-instance witness/miss
endpoint. Keep inverse generation, class counts/matching, smaller-side retention,
reuse/release and global computed-balance bit resources explicit in the next handoff.
`SortedMeet.original_machine` now supplies an interpreter-free full-state
whole-input witness/miss route using actual forward generation and reversed,
complemented inverse generation. Its sorted tagged matcher preserves packed
witnesses through collisions and proves exhaustive misses. Inspect
`sourceCertificate` for the composed preparation, arrays, tagging/sort/scan,
callback temporaries and decoded output charges. Both half lists are materialized;
the projection parameter does not choose smaller retained classes in this route.
Do not report its general composed profiles as sharp global source bounds or
as the class-count/orientation/deletion/reuse algorithm. Reuse this actual
matching stage when integrating bounded class batches; keep simultaneous full
state/payload storage and transient workspace charged. The old compacting
interpreter's cubic filter has not changed.
`ClassStreaming.run` now executes a count-only maximum prepass, computed smaller-side
retention, actual radix sorting of that class and singly evaluated opposite-side
probing. Only the input, counter and optional hit pass between classes. Its
original-input machine returns the computed maximum and decoded witness/miss;
list-prefix and physical wire bounds are proved from actual occurrence counts.
Keep those retained-value bounds separate from the composed callbacks' polynomial
auxiliary-workspace charges. This route rescans half words for every class and
uses linear retained-list lookup, so it is not the source's efficient projected
quarter-join/count-table realization. Handoffs must retain that time gap and the
unproved sharp global bit peak-space bound, even though full half-space arrays
are absent from this implementation.

`BatchedAccess.run` now sorts/matches bounded opposite-side batches with capacity
computed as retained count plus one, then clears them, including a final partial
flush. Retention and buffer insertion use structural linear machines; polynomial
callbacks operate on scalars or original-input/single-record data. Its actual
uniform original-input certificate includes all phase buffers and readback.
Do not turn the amortized record-volume bound into a bit-time theorem: the
current counter machine copies captured retained state and the growing buffer,
so the pair-count envelope can persist through copying even without per-record
lookup. Repeated class/count scans and the simultaneous global bit-resource proof
also remain open. Preserve these charges when requesting producer/consumer fusion
or persistent retained tapes; the old implementations have not changed.

`GroupedQuarter.run` now executes original-input quarter preparation/generation,
sorting and one-pass equal-key grouping. The group writer holds only a previous
key and emits nested frames directly; its actual prefix/callback bounds avoid a
growing-group accumulator. Its input/output quarter volume is still charged,
with a proved quarter-scale uniform time/space bound. Do not equate first-quarter
buckets with complete two-quarter classes or their maximum balance.
`ClassJoin` composes quarter-query generation and grouping with counted
occurrence joins. `ClassBalance` now derives unique complete half words, exact
forward/backward counter counts and the computed balance, then generates only
the count-selected smaller class. `JoinedDissection.run` is the assembled
original-input route through generated retention, opposite-quarter batch probing,
fixed outer release/iteration and original witness readback. Its correctness and
returned balance are proved; use both complete new clients linked in the
Operator's Manual when handing it over. The installed count certificate now
feeds the sorted quarter records directly to `KeyCount.run`, bypassing grouped
materialization in both directions. Its one-key/three-counter state has proved
near-linear record bit time and small callback prefix space, including binary
count widths. Retention now uses `KeyJoinStream.join_computable`: actual side
filters and nested streaming charge run replays to emitted pairs, avoiding the
whole-group polynomial join callback. Its charged prefix space includes filtered
runs, current group, callback tapes and materialized class output; the selected
join volume is derived from quarter sizes and computed balance. These phase
bounds do not establish the whole solver bound. `JoinedProbe` now consumes actual
opposite quarter groups with nested occurrence folds and immediate full-state
batch feeds, avoiding per-class half-space scans. The solver now selects a direct
whole-class match when computed counts bound its larger list by retained size
plus a quarter allowance; it does not materialize an arbitrary larger class.
Empty retained dictionaries skip opposite generation by matcher soundness. Its
certificate uses the encoded streaming kernel with actual finite-prefix maxima,
not supplied completion/resource assumptions. `sum_pairVisits` bounds total
class pair population by the two half populations; it is not a bit-time theorem.
The installed fallback now uses `ClassBatches`: completed row-aligned windows
are generated without retained dictionary/growing-buffer callback state, matched,
and released. Use the complete restarted-batch client alongside the original-input
client; the old online consumer remains available as a separate component.

The actual solver balance prepass now streams one scalar maximum of computed
count minima; no count table/reversal/reduction is executed. Its derived prefix
bit width and equality with the table-defined balance are checked. The direct
branch removes per-pair dictionary/buffer copies for fitting classes and has a
quarter-plus-balance logical prefix wire bound. The source allowance is at most
`11*2^k`. Preparation, half-array construction and final decoding have proved polynomial physical-input
resource bounds on the actual searched output. These are boundary phases only.

Keep its resource limits visible: separate count-table and retained/live-buffer prefix
encodings have derived bounds, but actual machine profiles also charge
repeated quarter/count generation, per-batch retained-parameter copies and all
callback tapes. Capacity includes quarter volume; `copyAllowance` and
`sum_restartCopyWork` derive the global repeated-input volume, while
`restart_prefix_wire` derives logical dictionary/output prefix wire. Neither is
a closed global bit-time/auxiliary-space theorem. Each
consumer list is read once; time sums actual rounds, while space takes actual
callback/prefix-state/token maxima and separately charges returned state. The
all-class search uses that same fixed kernel with actually generated index data,
whose `2^p(2p+1)` wire is quarter scale at the capped source depth. Class work is
summed and only a found pair survives a released class. The remaining bound
normalization must still bound actual count/quarter/window/full-state callbacks
in scalar widths, with simultaneous lifetimes. `SortedMatchBounds.runCertificate_bounds`
and `MatcherResources.original_restart_bounds` now close the installed fallback matching
component: actual tagging/sorting/scan clocks, argument copies, all-class/batch
clock sum and every matching-prefix workspace are bounded in original physical
widths. Build the complete restarted client for this result; it includes both
orientations and non-unit-width collision records. These are matching-only
profiles, not a global source resource theorem.
`ProducerResources` additionally normalizes installed quarter-generation/sort/count
allowances in physical scalar widths. Its all-class count phase and counts repeated
at every generated restart label include real recomputation. It also sums actual
full-state reconstruction allowances and bounds each reconstruction prefix, deriving
pair widths from original quarter witnesses. Reuse these results with the matcher
bounds; do not redo them or charge those phases as unit-cost input volume. The
window scan/cut/division, retained/group emission and internal class-search
control/ambient frames still need complete normalization.
`WholeRunResources.sourceCertificate_bounds` now composes the actual original-input
certificate through decoding. Its residual costs are explicitly the installed balance
certificate and the sum/max of installed class searches, with only original-input-width
polynomial and class-label overhead. The outer loop's captured state/copies/labels are
charged using `NativeCertificate.foldlStream_bounds`; its workspace uses prefix maxima,
and parked witness widths are derived from original soundness. `BalanceResources`
now normalizes the complete installed scalar prepass, including both count callbacks,
min/max, label generation, copies and every prefix. At the actual source cut it fits
half-exponential time and quarter-exponential workspace in original input widths.
`sourceCertificate_search_bounds` composes this into the unchanged whole run; only
class-search sum/max remain explicit costs in that envelope. `SearchResources` now
normalizes generated class pairs/full states and selected direct searches, including
orientation/materialization and both producer/matcher temporaries. Its whole-source
composition leaves only the selected restarted-search sum/max explicit, including
classes skipped after hits. Next normalize those actual restarted-window, label/control,
callback/frame and simultaneous workspace costs; do not repeat the completed prepass,
direct branch or envelope proofs. The residuals are cost expressions, not runtime
hypotheses or sharp whole-run bounds. The direct-only checked client is not a general
restart theorem; the fallback guard verifies that its costs have not disappeared.
Orientation recomputes counts; no cached-size oracle is input. The faster source
reachable-state-DP all-count and quarter-time prepass remain separate open endpoints.
Do not promote pair/batch traversal sums or unnormalized machine profiles to
sharp source TM bounds. The per-pair copy path is no longer installed, but sharp
global inequalities remain required. The old solvers and
all their charges remain intact; the new direct route bypasses their interpreter.

## Correct course and hand work over

When an agent drifts, name the mismatch: the theorem became conditional, the model changed, the
example cannot be followed, or the task expanded beyond the agreed scope. Ask it to preserve
the useful work, state the remaining objective and return to a concrete next step. When two
agents overlap, have the coordinator resolve ownership before either overwrites the other's work.

For a handoff, request the issue and PR, branch and revision, actual validation, review state,
remaining work and the next action. Put that record in the issue/PR or commit, according to the
[durable-record rules](../AGENTS.md#durable-records). A new agent should inspect those records
and the current source before resuming. Silence alone does not release another agent's task.

To stop, specify which task or session should stop and ask for a preserved checkpoint and
handoff. Agents should stop only processes they own. An ended session cannot promise unattended
progress. You can resume from the recorded state with a new assignment.

Both manuals are maintained with the library under
[Maintaining the manuals](../CONTRIBUTING.md#maintaining-the-manuals). If an instruction here
cannot be followed, treat that as a documentation defect for the responsible worker and
coordinator to fix and review.
