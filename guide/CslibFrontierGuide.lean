/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import CslibFrontierGuide.FirstSteps
import CslibFrontierGuide.NPCompleteness
import CslibFrontierGuide.Streaming
import CslibFrontierGuide.FirstOrderOperators

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "A Guide to cslib-frontier" =>
%%%
shortTitle := "cslib-frontier guide"
%%%

cslib-frontier is the frontier formalization library for [CSLib][cslib], built on CSLib and
Mathlib; its scope is computer science generally, from algorithms and data structures to
complexity, cryptography and logic. This guide introduces the library one area at a time, in the
order a newcomer needs it: what the objects are, how to state an ordinary claim, and how to prove
one. Every Lean example is elaborated against the library when the guide is built, so an example
that no longer matches the library fails the build.

Names in the examples link to the [API documentation][api], which lists every declaration with its
docstring and source. Other entry points:

* The README's [Start here][start] table points to checked examples for each kind of task.
* The [results inventory][results] collects named results with their theorem names and sources.
* [ROADMAP.md][roadmap] records outstanding work, and [CONTRIBUTING.md][contributing] explains how
  to propose and review changes.

The guide is new: after first steps, it has chapters on NP-completeness, streaming, and first-order
logic with operators. Further areas follow one at a time, and each chapter's friction points are
fixed in the library rather than documented around.

[cslib]: https://github.com/leanprover/cslib
[api]: https://www.cslib.io/cslib-frontier/
[start]: https://github.com/cslib-community/cslib-frontier#start-here
[results]: https://github.com/cslib-community/cslib-frontier/blob/main/results/README.md
[roadmap]: https://github.com/cslib-community/cslib-frontier/blob/main/ROADMAP.md
[contributing]: https://github.com/cslib-community/cslib-frontier/blob/main/CONTRIBUTING.md

{include 1 CslibFrontierGuide.FirstSteps}

{include 1 CslibFrontierGuide.NPCompleteness}

{include 1 CslibFrontierGuide.Streaming}

{include 1 CslibFrontierGuide.FirstOrderOperators}
