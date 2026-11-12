/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (structure-encoding visibility regression tests)

public import CslibFrontierTests.StructureEncodingVisibility

/-! Import-side clients and visibility checks for every generated declaration. -/

open Turing.MultiTapeTM CslibFrontierTests.StructureEncoding
open CslibFrontierTests.StructureEncodingVisibility

noncomputable section

-- Default-public constructor and field rules survive an import for an applied structure.
example {n : ℕ} :
    ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk t.tag t.entries)
      encPublicTable encPublicTable := by
  have hid : ComputableInPolyTime (fun t : TaggedTable n => t) encPublicTable encPublicTable := by
    fun_prop
  exact encPublicTable_mk_polyTime
    (encPublicTable_tag_polyTime hid) (encPublicTable_entries_polyTime hid)

-- Flipping the tag is a real update, so automation must construct and read the record.
example {n : ℕ} :
    ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk (!t.tag) t.entries)
      encPublicTable encPublicTable := by
  fun_prop

example {n : ℕ} :
    ComputableInPolyTime (fun t : TaggedTable n => !t.tag) encPublicTable encBool := by
  have hflip :
      ComputableInPolyTime (fun t : TaggedTable n => TaggedTable.mk (!t.tag) t.entries)
        encPublicTable encPublicTable := by
    fun_prop
  exact encPublicTable_tag_polyTime hflip

example : ComputableInPolyTime (TaggedTable.tag (n := 0)) encPublicTable encBool := by
  have hid : ComputableInPolyTime (fun t : TaggedTable 0 => t) encPublicTable encPublicTable := by
    fun_prop
  exact encPublicTable_tag_polyTime hid

end

-- Check the whole generated family, including constructor/field budgets and linear rules.
run_cmd do
  let env ← Lean.getEnv
  let suffixes := ["", "Fields", "_apply", "_fields_deg", "_mk_deg", "_mk_inO",
    "_mk_budget", "_mk_polyTime", "_tag_deg", "_tag_inO", "_tag_budget", "_tag_polyTime",
    "_entries_deg", "_entries_inO", "_entries_budget", "_entries_polyTime"]
  for suffix in suffixes do
    let visible :=
      (`CslibFrontierTests.StructureEncodingVisibility.encPublicTable).appendAfter suffix
    let hidden :=
      (`CslibFrontierTests.StructureEncodingVisibility.encPrivateTable).appendAfter suffix
    unless env.contains visible do
      throwError "default-public enc_structure did not export {visible}"
    if env.contains hidden then
      throwError "private enc_structure exported {hidden}"
