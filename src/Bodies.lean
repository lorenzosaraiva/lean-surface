import Lean
open Lean Meta

namespace BodyErasure

def node (kind : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("kind", toJson kind) :: fields)

partial def levelTree (params : List Name) : Level → Json
  | .zero => node "zero"
  | .succ l => node "succ" [("of", levelTree params l)]
  | .max a b => node "max" [("left", levelTree params a), ("right", levelTree params b)]
  | .imax a b => node "imax" [("left", levelTree params a), ("right", levelTree params b)]
  | .param n => node "parameter" [("index", toJson (params.idxOf n))]
  | .mvar _ => node "unresolved-universe"

/- Work in the original typing context. Only proof-valued expressions are erased.
   Propositions themselves, types, constants and computation remain structural.
   Binder names and metadata are ignored; bound variables use de Bruijn indices.
   No unfolding, reduction or definitional-equality test is performed. -/
partial def erase (e : Expr) (params : List Name) (bound : Array FVarId := #[]) : MetaM Json := do
  if let .mdata _ e := e then return ← erase e params bound
  if ← isProof e then return node "proof-placeholder"
  match e with
  | .bvar _ => throwError "unexpected loose bound variable"
  | .mvar _ => throwError "unresolved expression metavariable"
  | .fvar id =>
    let some i := bound.toList.reverse.idxOf? id | throwError "unexpected free variable"
    return node "bound" [("index", toJson i)]
  | .sort l => return node "sort" [("level", levelTree params l)]
  | .const n ls => return node "constant" [("name", toJson n.toString),
      ("levels", toJson (ls.map (levelTree params)))]
  | .app f a => return node "application" [("fn", ← erase f params bound), ("arg", ← erase a params bound)]
  | .lam n t b bi =>
    let type ← erase t params bound
    withLocalDecl n bi t fun x => do
      return node "lambda" [("type", type), ("binder", toJson (toString (repr bi))),
        ("body", ← erase (b.instantiate1 x) params (bound.push x.fvarId!))]
  | .forallE n t b bi =>
    let type ← erase t params bound
    withLocalDecl n bi t fun x => do
      return node "forall" [("type", type), ("binder", toJson (toString (repr bi))),
        ("body", ← erase (b.instantiate1 x) params (bound.push x.fvarId!))]
  | .letE n t v b _ =>
    let type ← erase t params bound
    let value ← erase v params bound
    withLetDecl n t v fun x => do
      return node "let" [("type", type), ("value", value),
        ("body", ← erase (b.instantiate1 x) params (bound.push x.fvarId!))]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .proj s i e => return node "projection" [("structure", toJson s.toString),
      ("index", toJson i), ("of", ← erase e params bound)]
  | .mdata _ _ => throwError "metadata not stripped"

def bodies (names : List String) : MetaM Json := do
  let mut rows := #[]
  for name in names do
    let ci ← getConstInfo name.toName
    let .defnInfo defn := ci | throwError "body root is not a definition: {name}"
    if defn.safety == .unsafe then throwError "unsafe body root refused: {name}"
    let erased ← erase defn.value ci.levelParams
    rows := rows.push (Json.mkObj [("name", toJson name), ("erased", erased)])
  return toJson rows

end BodyErasure

unsafe def main (args : List String) : IO UInt32 := do
  let mod :: out :: names := args | return 2
  try
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let options := ({} : Options).set `maxRecDepth (10000 : Nat) |>.set `maxHeartbeats (0 : Nat)
    let env ← importModules #[{ module := mod.toName }] options (loadExts := true) (level := .private)
    let result ← (MetaM.run' (BodyErasure.bodies names)).toIO'
      { fileName := "Bodies.lean", fileMap := default, options := options } { env := env }
    IO.FS.writeFile out (result.pretty ++ "\n")
    return 0
  catch e =>
    IO.eprintln s!"body check failed: {e}"
    return 1
