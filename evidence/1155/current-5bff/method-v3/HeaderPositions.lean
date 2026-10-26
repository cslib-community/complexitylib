/- Diagnostic-only source positions from Lean's own module-header parser. -/
import Lean.Parser.Module
import Lean.Data.Json

open Lean

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let paths ← IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse input)) :
    Except String (Array String))
  let mut rows : Array Json := #[]
  for path in paths do
    let text ← IO.FS.readFile path
    let (header, state, messages) ← Parser.parseHeader (Parser.mkInputContext text path)
    if messages.hasErrors then throw (IO.userError s!"header parse error: {path}")
    let env ← mkEmptyEnvironment
    let mut prefixState := state
    let mut install := state.pos
    let mut foundDoc := false
    let mut scan := true
    while scan do
      let (command, next, errors) := Parser.parseCommand
        (Parser.mkInputContext text path) { env := env, options := {} } prefixState {}
      if !errors.hasErrors && command.isOfKind ``Parser.Command.moduleDoc then
        install := next.pos
        foundDoc := true
        scan := false
      else if !errors.hasErrors && command.isOfKind ``Parser.Command.set_option &&
          next.pos.byteIdx > prefixState.pos.byteIdx then
        install := next.pos
        prefixState := next
      else
        scan := false
    rows := rows.push <| Json.mkObj [
      ("path", toJson path), ("header_end_byte", toJson state.pos.byteIdx),
      ("header_kind", toJson header.raw.getKind.toString),
      ("install_byte", toJson install.byteIdx), ("leading_module_doc", toJson foundDoc)]
  IO.println (toJson rows).compress
