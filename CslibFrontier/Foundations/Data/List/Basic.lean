/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.Append
public import CslibFrontier.Foundations.Data.List.Counting
public import CslibFrontier.Foundations.Data.List.Fold
public import CslibFrontier.Foundations.Data.List.Lookup

/-!
# List identities

Re-export the fold, lookup, counting and append APIs. New consumers should import the topic
module they use; this module keeps the existing combined import available.
-/
