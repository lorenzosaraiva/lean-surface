/- Native trusted-cache driver. Comparison and replay are upstream APIs.
   This driver makes no sandbox claim. -/
import Comparator
import Lean4Checker.Replay
import Export.Parse
open Lean

def readExport (path : String) : IO Export.ExportedEnv := do
  let ref ← IO.mkRef { data := (← IO.FS.readFile path).toByteArray }
  Export.parseStream (IO.FS.Stream.ofBuffer ref)

def main (args : List String) : IO UInt32 := do
  let [cfgPath, challengePath, solutionPath] := args | return 2
  try
    let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
    let names (key : String) : IO (Array Name) := do
      let xs ← IO.ofExcept ((← IO.ofExcept (cfg.getObjVal? key)).getArr?)
      xs.mapM fun x => return (← IO.ofExcept x.getStr?).toName
    let theorems ← names "theorem_names"
    let definitions ← names "definition_names"
    let axioms ← names "permitted_axioms"
    let challenge ← readExport challengePath
    let solution ← readExport solutionPath
    let primitive := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
      ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,
      ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList]
    IO.ofExcept (Comparator.compareAt challenge solution (theorems ++ axioms) definitions primitive)
    IO.ofExcept (Comparator.checkAxioms solution theorems definitions axioms)
    IO.println "Comparator comparison and axiom checks: PASS"
    let env ← Lean.mkEmptyEnvironment
    let constants := solution.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
    discard (env.replay' constants)
    IO.println "Lean kernel replay: PASS"
    return 0
  catch e =>
    IO.eprintln s!"Comparator rejected: {e}"
    return 1
