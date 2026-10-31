/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import ComplexityGuide.FirstSteps
import ComplexityGuide.NPCompleteness
import ComplexityGuide.Streaming
import ComplexityGuide.FirstOrderOperators

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "A Guide to Complexitylib" =>
%%%
shortTitle := "Complexitylib guide"
%%%

Complexitylib is a Lean 4 library of computational complexity theory, built on [CSLib][cslib] and
Mathlib. This guide introduces the library one area at a time, in the order a newcomer needs it:
what the objects are, how to state an ordinary claim, and how to prove one. Every Lean example is
elaborated against the library when the guide is built, so an example that no longer matches the
library fails the build.

Names in the examples link to the [API documentation][api], which lists every declaration with its
docstring and source. Other entry points:

* The README's [Start here][start] table points to checked examples for each kind of task.
* The [selected formal abstracts][abstracts] state the library's headline results with every
  definition they use, also as [PDFs][pdfs].
* [ROADMAP.md][roadmap] records outstanding work, and [CONTRIBUTING.md][contributing] explains how
  to propose and review changes.

The guide is new: after first steps, it has chapters on NP-completeness, streaming, and first-order
logic with operators. Further areas follow one at a time, and each chapter's friction points are
fixed in the library rather than documented around.

[cslib]: https://github.com/leanprover/cslib
[api]: https://www.cslib.io/complexitylib/
[start]: https://github.com/cslib-community/complexitylib#start-here
[abstracts]: https://github.com/cslib-community/complexitylib/blob/main/abstracts/README.md
[pdfs]: https://www.cslib.io/complexitylib/abstracts/catalogue.pdf
[roadmap]: https://github.com/cslib-community/complexitylib/blob/main/ROADMAP.md
[contributing]: https://github.com/cslib-community/complexitylib/blob/main/CONTRIBUTING.md

{include 1 ComplexityGuide.FirstSteps}

{include 1 ComplexityGuide.NPCompleteness}

{include 1 ComplexityGuide.Streaming}

{include 1 ComplexityGuide.FirstOrderOperators}
