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
    rows := rows.push <| Json.mkObj [
      ("path", toJson path), ("header_end_byte", toJson state.pos.byteIdx),
      ("header_kind", toJson header.raw.getKind.toString)]
  IO.println (toJson rows).compress
