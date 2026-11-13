/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Basic
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Memory

/-!
# Runtime word encodings for the memory heap

Every native method uses the existing dependent `Memory.Layout`, including its runtime number
of handles. The size address/length and array base remain values, rather than selecting code.
The same encoding is shared by both sifts and the finite family of operation bodies.

## Main definitions

* `HeapLayout`, `layoutWords`: the existing layout and its faithful four-word encoding.
* `IndexArgument`, `indexWords`: append a runtime heap position to the layout.
* `HandleArgument`, `handleWords`: the same word vector for a typed valid handle.

## Implementation notes

The native arguments are nested pairs read through named `abbrev` accessors such as
`IndexArgument.layout`, not structures. `realize` matches a call such as `Memory.insert L v k`
against a certificate by expanding only `Prod` and `Sigma` arguments (`callArgument`), so a
structure argument would no longer match the plain-argument call sites in `Extract` and in
Dijkstra's native client.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM.Realization

/-- The existing dependent layout, including the runtime number of handles. -/
abbrev HeapLayout := Σ n, Memory.Layout n

/-- The runtime layout has a faithful four-word representation. -/
def layoutWords : HeapLayout ↪ (Fin 4 → ℕ) where
  toFun d := ![d.1, d.2.size.base, d.2.size.length, d.2.base]
  inj' := by
    rintro ⟨n, ⟨⟨b, l⟩, a⟩⟩ ⟨n', ⟨⟨b', l'⟩, a'⟩⟩ h
    have hn : n = n' := by simpa using congrFun h 0
    have hb : b = b' := by simpa using congrFun h 1
    have hl : l = l' := by simpa using congrFun h 2
    have ha : a = a' := by simpa using congrFun h 3
    subst n'; subst b'; subst l'; subst a'
    rfl

/-- A runtime layout with a heap position or handle word. -/
abbrev IndexArgument := HeapLayout × ℕ

namespace IndexArgument

/-- The runtime heap layout with its capacity. -/
abbrev heap (d : IndexArgument) : HeapLayout := d.1

/-- The number of handles. -/
abbrev capacity (d : IndexArgument) : ℕ := d.1.1

/-- The heap layout. -/
abbrev layout (d : IndexArgument) : Memory.Layout d.capacity := d.1.2

/-- The heap position or handle word. -/
abbrev index (d : IndexArgument) : ℕ := d.2

end IndexArgument

/-- Faithful runtime layout and heap position. -/
abbrev indexWords := appendWords layoutWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- A valid handle packaged with the runtime layout; no new layout or machine state is added. -/
abbrev HandleArgument := Σ n, Memory.Layout n × Fin n

namespace HandleArgument

/-- The number of handles. -/
abbrev capacity (d : HandleArgument) : ℕ := d.1

/-- The heap layout. -/
abbrev layout (d : HandleArgument) : Memory.Layout d.capacity := d.2.1

/-- The valid handle. -/
abbrev handle (d : HandleArgument) : Fin d.capacity := d.2.2

/-- Forget the handle's bound, keeping its word. -/
abbrev toIndex (d : HandleArgument) : IndexArgument := (⟨d.capacity, d.layout⟩, d.handle.val)

end HandleArgument

/-- The typed handle reuses the same layout/index encoding by faithful inclusion. -/
def handleWords : HandleArgument ↪ (Fin 5 → ℕ) :=
  ({ toFun := HandleArgument.toIndex
     inj' := by
       rintro ⟨n, L, v⟩ ⟨n', L', v'⟩ h
       have hL := congrArg Prod.fst h
       have hv := congrArg Prod.snd h
       cases hL
       have he : v = v' := Fin.ext hv
       cases he
       rfl } : HandleArgument ↪ IndexArgument).trans indexWords

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
