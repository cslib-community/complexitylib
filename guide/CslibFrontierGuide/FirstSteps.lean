/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import CslibFrontier.Computability.Complexity.Classes.NP

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "First Steps" =>
%%%
tag := "first-steps"
%%%

The package is named `cslib-frontier`, and its modules begin with `CslibFrontier.` and mirror CSLib's
layout. `import CslibFrontier` imports the whole library, which is convenient for exploring but slow
to load; a development imports the modules it uses. Each module's documentation lists its main
definitions and results, with references.

Declarations use CSLib's namespaces. Turing machines, encodings and polynomial-time computability
live under `Turing`, and complexity classes, problems and reductions under `Cslib.Complexity`.
For example, this chapter imports `CslibFrontier.Computability.Complexity.Classes.NP`, which defines
the class {name}`Cslib.Complexity.NP` in terms of
{name}`Turing.MultiTapeTM.ComputableInPolyTime`:

```lean (name := npType)
#check @Cslib.Complexity.NP
```
```leanOutput npType
@Cslib.Complexity.NP : {α : Type} → (α ↪ List Bool) → Set (Set α)
```

To find a declaration, search the
[API documentation](https://www.cslib.io/cslib-frontier/search.html). In this guide,
hovering over a name shows its type and docstring, and clicking it opens its entry there.
