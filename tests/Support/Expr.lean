/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, Edward Ayers, Arthur Paulino, Thomas R. Murrills
-/
module

public import Lean

public meta section
namespace Lean.Expr
open Lean.Meta

/-- If `e` is a projection of the structure constructor, reduce the projection.
Otherwise returns `none`. If this function detects that expression is ill-typed, throws an error.
For example, given `Prod.fst (x, y)`, returns `some x`. -/
def reduceProjStruct? (e : Expr) : MetaM (Option Expr) := do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
    -- Check that the structure is a constructor expression.
    unless sarg.getAppFn.isConstOf pinfo.ctorName do
      return none
    let sfields := sarg.getAppArgs
    -- The ith projection extracts the ith field of the constructor
    let sidx := pinfo.numParams + pinfo.i
    if hs : sidx < sfields.size then
      return some (sfields[sidx]'hs)
    else
      throwError m!"ill-formed expression, {cname} is the {pinfo.i + 1}-th projection function \
        but {sarg} does not have enough arguments"
  else
    return none

end Lean.Expr
