# cslib-frontier Operator's Manual

This is the substantial manual for humans or agents using, changing and reviewing the
cslib-frontier codebase. It explains models, tactics, proof interfaces, design and development
procedures. It assumes basic Lean literacy; a human should be able to follow the workflows
with a text editor, Git, Python and Lake. AI tools are optional.

The separate [Agent Operator's Manual](AGENT_OPERATORS.md) is a short guide for the human
driving agents: choosing roles, assigning work, requesting review, handing off and intervening.
Use that manual to direct a session, and this manual for the codebase operations performed
within it.

Start with [getting a checkout and checking a complete client](workflows/getting-started.md).
The [first contribution exercise](workflows/getting-started.md#a-first-worked-example)
leads from an isolated branch through a successful check, an expected failure, its repair,
and a reviewable handoff. [Choose a model](workflows/choosing-models.md) before stating a
resource bound: the encoding and cost convention are part of the theorem.

| Task | Route |
|---|---|
| Build, inspect and change a first client | [Get started](workflows/getting-started.md) |
| State a model and resource contract | [Choose a model](workflows/choosing-models.md) |
| Compose deterministic certificates or prove P/NP membership | [Deterministic workflows](workflows/deterministic-workflows.md) |
| Write randomized or oracle programs and prove efficiency | [Probabilistic workflows](workflows/probabilistic-workflows.md) |
| Locate a theorem and check its assumptions | [Find results](workflows/finding-results.md) |
| Understand a failed proof or build | [Troubleshoot](workflows/troubleshooting.md) |
| Prepare, validate and review a change | [Contribute and review](workflows/contributing.md) |
| Look up a command or term | [Commands and vocabulary](COMMANDS.md) |
| Coordinate implementation and review | [Participant and reviewer procedures](workflows/agent-operations.md) |
| Direct agents as their human operator | [Agent Operator's Manual](AGENT_OPERATORS.md) |

The [reference index](index.md) covers models, major theorems, design choices and source
credit. The [model map](model-map.md) provides 265 model and interface entries from the
initial survey. Update the affected descriptions and routes when an interface, theorem
contract or operating procedure changes; the index is not a claim that every mathematical
declaration has been classified. The [existing guide](../guide/CslibFrontierGuide.lean) remains
the home of its checked narrative examples, and [library source](../CslibFrontier/) and
[tests](../CslibFrontierTests/) remain the authority for definitions and example bodies.

## Maintain both manuals with the code

Every change needs an impact assessment for both manuals under the
[contribution policy](../CONTRIBUTING.md#maintaining-the-manuals). Update affected procedures,
reference claims, source links and examples in the same change, or give a concrete no-impact
reason for each manual. Coordinator review of both assessments is mandatory, with independent
review of the affected content against the final revision. Read the [maintenance procedure](MAINTAINING.md) for
what to inspect and how to validate it.

```bash
python3 scripts/check_operator_manual.py
python3 scripts/test_operator_manual.py
```

Run these commands from the repository root. The first checks local links, visual markup, the
book's chapter lists and the identity of contextual Lean excerpts against the current source;
the second exercises failure cases of that checker. Neither compiles Lean or establishes that
the prose describes the right mathematics. Check affected complete clients through Lake as the
workflows describe.

## Read or build the manuals

Markdown is canonical and readable directly in the checkout. To generate the editable
LaTeX source and PDF for each manual:

```bash
python3 scripts/build_operator_manual.py
python3 scripts/build_operator_manual.py --agent-manual
```

The [build instructions](BUILD.md) list optional publishing tools and output locations.
Book products live under ignored `manual/_build/`; optional research exports use
`manual/_generated/`. Neither is maintained by hand.

## Dated evidence

The initial source survey and development measurements were taken at
`13e6a31951bf1c89a1a6258c44f9444aecbbefd8` on 2 November 2026. The reference chapters retain
pinned source evidence for that baseline; changes to their claims need current evidence.
The [development record](development-history/index.md), census, transcript excerpts and
historical audit data remain dated observations. Do not silently update their denominators
or make old validation evidence support a new revision. Desktop conversation records are
absent from that dataset. Raw private transcripts are not included.
