/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable embeddings out of countable spaces

On a countable space with measurable singletons every set is countable, hence measurable. So an
injective map from such a space into a space with measurable singletons is measurable, and it
sends every set to a countable, hence measurable, set: it is a measurable embedding. This removes
the measurability side conditions when transferring measures and integrals along an injection of a
finite or countable space, for instance a finite subdomain or a finite cube of signs.

## Main results

* `MeasurableEmbedding.of_countable`: an injective map from a countable space with measurable
  singletons into a space with measurable singletons is a measurable embedding.
-/

public section

/-- An injective map from a countable space with measurable singletons into a space with
measurable singletons is a measurable embedding: every set of the source is countable, and so is
its image. -/
theorem MeasurableEmbedding.of_countable {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : α → β} (hf : Function.Injective f) : MeasurableEmbedding f where
  injective := hf
  measurable := .of_discrete
  measurableSet_image' _ _ := ((Set.to_countable _).image f).measurableSet
