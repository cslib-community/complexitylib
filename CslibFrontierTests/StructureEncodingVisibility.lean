/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (structure-encoding visibility regression tests)

public import CslibFrontierTests.StructureEncoding

/-!
# Default-public and private encodings of an applied structure

Reuse the parameterized table fixture. Neither encoding is inside a `public section`, so the
importing client checks the command's default visibility. The private rules are exercised here.
-/

namespace CslibFrontierTests.StructureEncodingVisibility

open Turing.MultiTapeTM CslibFrontierTests.StructureEncoding

noncomputable section

variable {n : ℕ}

/-- A public encoding of the existing table, with its framed tag before its entries. -/
enc_structure encPublicTable : TaggedTable n where
  tag : encBool, entries : (encPi (Index := Fin n) encNat)

/-- An implementation encoding with the same layout and private generated declarations. -/
private enc_structure encPrivateTable : TaggedTable n where
  tag : encBool, entries : (encPi (Index := Fin n) encNat)

-- Reading both fields and rebuilding a private-encoded record uses the generated rules.
example : ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk t.tag t.entries)
    encPrivateTable encPrivateTable := by
  have hid : ComputableInPolyTime (fun t : TaggedTable n => t) encPrivateTable encPrivateTable := by
    fun_prop
  exact encPrivateTable_mk_polyTime
    (encPrivateTable_tag_polyTime hid) (encPrivateTable_entries_polyTime hid)

-- Flipping the tag is a real update, so automation must construct and read the record.
example {n : ℕ} :
    ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk (!t.tag) t.entries)
      encPrivateTable encPrivateTable := by
  fun_prop

example {n : ℕ} :
    ComputableInPolyTime (fun t : TaggedTable n => !t.tag) encPrivateTable encBool := by
  have hflip :
      ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk (!t.tag) t.entries)
        encPrivateTable encPrivateTable := by
    fun_prop
  exact encPrivateTable_tag_polyTime hflip

-- The parameter remains fixed even for a field that does not mention it, including size zero.
example : ComputableInPolyTime (TaggedTable.tag (n := 0)) encPrivateTable encBool := by
  have hid : ComputableInPolyTime (fun t : TaggedTable 0 => t) encPrivateTable encPrivateTable := by
    fun_prop
  exact encPrivateTable_tag_polyTime hid

example (t : TaggedTable n) :
    encPrivateTable t = encPair encBool (encPi encNat) (t.tag, t.entries) := rfl

end

/-- A private encoding with an explicit parameter and a dependent field. -/
private enc_structure encPrivateElement (F : Family) : Element F where
  size : encUnary, desc : F.encDesc, elt : (F.encode desc) using (F.encode_injective desc)

example (F : Family) (x : Element F) :
    encPrivateElement F x =
      encPair encUnary (encPair F.encDesc encBits) (x.size, x.desc, F.encode x.desc x.elt) :=
  rfl

-- Rebuilding a record reads each field and builds the dependent word with the private rules.
example (F : Family) :
    ComputableInPolyTime (fun x : Element F => (⟨x.size, x.desc, x.elt⟩ : Element F))
      (encPrivateElement F) (encPrivateElement F) := by
  fun_prop

end CslibFrontierTests.StructureEncodingVisibility
