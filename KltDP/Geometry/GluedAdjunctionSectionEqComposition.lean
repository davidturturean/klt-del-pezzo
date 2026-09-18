import Lean

/-!
# Compose the original section equalities with their native endpoints

Only local-let/head-beta reductions and assigned metavariables are used
in the bounded structural guard. The result is an ordinary Eq.symm /
Eq.trans proof with explicit original carriers, checked by Lean's kernel.
-/
open Lean Meta Elab Tactic
namespace KltDP.Geometry.GluedAdjunctionSectionEqComposition

private partial def localHead (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if fuel == 0 then return e
  match e with
  | .letE _ _ value tail _ => localHead (tail.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    match decl.value? with
    | some value => localHead value (fuel - 1)
    | none => return e
  | _ => return e

private def equation (ty : Expr) : MetaM (Expr × Array Expr) := do
  let ty ← localHead ty
  unless ty.getAppFn.constName? == some ``Eq && ty.getAppArgs.size == 3 do
    throwError "section equality composition: expected an equality"
  return (ty.getAppFn, ty.getAppArgs)

private def sameNative (x y : Expr) : MetaM Unit := do
  let mut pending := #[(x, y)]
  let mut visits := 0
  while !pending.isEmpty && visits < 512 do
    let (a, b) := pending.back!
    pending := pending.pop
    visits := visits + 1
    let a ← localHead a
    let b ← localHead b
    if a == b then continue
    unless a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size do
      throwError "section equality composition: native endpoints differ after local reduction"
    for i in [:a.getAppArgs.size] do
      pending := pending.push (a.getAppArgs[i]!, b.getAppArgs[i]!)
  unless pending.isEmpty do
    throwError "section equality composition: native comparison exceeds 512 nodes"

elab "close_native_section_eq " hR:ident hE:ident hT:ident : tactic => withMainContext do
  let pr ← instantiateMVars (← Term.elabTerm hR none)
  let pe ← instantiateMVars (← Term.elabTerm hE none)
  let pt ← instantiateMVars (← Term.elabTerm hT none)
  let (head, r) ← equation (← inferType pr)
  let (_, e) ← equation (← inferType pe)
  let (_, t) ← equation (← inferType pt)
  sameNative r[0]! e[0]!
  sameNative e[0]! t[0]!
  sameNative r[1]! e[1]!
  sameNative e[2]! t[1]!
  let .const _ levels := head | throwError "section equality composition: equality head"
  let reversed := mkAppN (mkConst ``Eq.symm levels) #[r[0]!, r[1]!, r[2]!, pr]
  let first := mkAppN (mkConst ``Eq.trans levels)
    #[r[0]!, r[2]!, r[1]!, e[2]!, reversed, pe]
  let proof := mkAppN (mkConst ``Eq.trans levels)
    #[r[0]!, r[2]!, e[2]!, t[2]!, first, pt]
  (← getMainGoal).assign proof
  replaceMainGoal []

end KltDP.Geometry.GluedAdjunctionSectionEqComposition
