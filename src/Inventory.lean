import Lean
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [mod, out] := args | return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := mod.toName }] {} (loadExts := true) (level := .private)
  let imported := env.allImportedModuleNames
  let target := mod.toName
  let some index := imported.findIdx? (· == target) | throw (IO.userError "module not found")
  let mut rows := #[]
  for ci in env.header.moduleData[index]!.constants do
    let n := ci.name
    let kind := match ci with
      | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
    let safety := match ci with
      | .defnInfo d => toString (repr d.safety)
      | .opaqueInfo d => if d.isUnsafe then "unsafe" else "safe"
      | _ => "safe"
    let mut related : Array Name := #[]
    match ci with
    | .inductInfo i => related := i.ctors.toArray ++ i.all.toArray
    | .ctorInfo i => related := #[i.induct]
    | .recInfo i =>
      for rule in i.rules do
        related := related ++ #[rule.ctor] ++ rule.rhs.getUsedConstants
    | _ => pure ()
    rows := rows.push (Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson kind), ("safety", toJson safety),
      ("type_dependencies", toJson (ci.type.getUsedConstants.map (·.toString))),
      ("related_constants", toJson (related.map (·.toString))),
      ("body_dependencies", toJson (ci.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[] |>.map (·.toString)))])
  rows := rows.qsort fun a b =>
    (a.getObjValAs? String "name").toOption.getD "" < (b.getObjValAs? String "name").toOption.getD ""
  IO.FS.writeFile out ((toJson rows).pretty ++ "\n")
  return 0
