# History

[Operator's Manual](../README.md) · [Reference index](../index.md)

cslib-frontier began as complexitylib, a Lean library of computational complexity theory built
on CSLib. On 2026-11-08 the repository was renamed and its scope widened to computer science
generally ([#3675](https://github.com/cslib-community/cslib-frontier/issues/3675)). The
pre-CSLib [complexitylib-v1](https://github.com/SamuelSchlesinger/complexitylib-v1) has a
different API; some of its developments remain to be ported.

This part keeps the dated record from the complexitylib period. It explains earlier decisions
and failures, but it does not describe the current library or govern current contributions:
use the [Operator's Manual](../README.md), [AGENTS.md](../../AGENTS.md) and
[CONTRIBUTING.md](../../CONTRIBUTING.md) for those.

- [The 2 November 2026 source survey](survey.md): the survey from which the reference chapters
  and model map grew, with its research questions, census, evidence rules, supporting scripts
  and limitations.
- [Automated development](development.md): what the repository history, CI records and
  available conversations show about human-directed automated development, with its
  [methods](methods.md), [timings](timings.md), [case studies](case-studies.md),
  [transcript excerpts](transcripts.md) and [study design](study-design.md).
- [Paper plan](paper-plan.md): the earlier academic framing of the survey. It is kept as
  editorial context and is not part of the book.

## Read dated evidence

The survey and the development measurements were taken at
`13e6a31951bf1c89a1a6258c44f9444aecbbefd8` on 2 November 2026, when the module root was
`Complexity/`. The census, transcript excerpts and historical audit data are observations at
that revision. Do not silently update their denominators or use old validation evidence to
support a new revision; a new measurement belongs in a separately dated observation. Desktop
conversation records are absent from the dataset, and raw private transcripts are not included.
