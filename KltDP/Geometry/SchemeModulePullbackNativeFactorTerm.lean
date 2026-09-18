import KltDP.Geometry.SchemeModulePullbackMapEqFactorNative
import Lean

/-!
# Explicit original native pullback-factor applications

This term elaborator reads only the supplied original witness and equality.
It fills every generic argument syntactically from their stored types and
returns an ordinary application of the proved nativeIso/nativeIso_comp.
Lean's kernel checks that application. No isDefEq, new axiom, typeclass search
for a reconstructed pullback, or declaration-wide traversal is used.
-/

open Lean Meta Elab Term

namespace KltDP.Geometry.SchemeModulePullbackNativeFactorTerm

private partial def headZeta (t : Expr) : Expr :=
  match t.consumeMData.headBeta with
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | t => t

private def unfoldNamedIso (e : Expr) : MetaM Expr := do
  let e := headZeta e
  let .const name levels := e.getAppFn | return e
  if !name.toString.endsWith ".leftFactorIso" &&
      !name.toString.endsWith ".rightFactorIso" then return e
  let info ← getConstInfo name
  let some value := info.value? | throwError "Original named factor has no stored value"
  return headZeta ((value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs)

private def equationArgs (h : Expr) : MetaM (Array Expr) := do
  let mut t := headZeta (← inferType h)
  for _ in [:4] do
    if t.isAppOfArity ``Eq 3 then return t.getAppArgs
    let .const name _ := t.getAppFn | throwError "Expected an original equality"
    unless name.toString.endsWith ".statementOf" && t.getAppArgs.size == 2 do
      throwError "Expected an original equality or its transparent statementOf"
    t := headZeta t.getAppArgs[0]!
  throwError "Original equality exceeded four transparent statement wrappers"

private def pullbackObjectParts (t : Expr) : MetaM (Expr × Expr) := do
  let args := (headZeta t).getAppArgs
  unless args.size ≥ 2 do throwError "Expected the original pullback object"
  let mut F := headZeta args[args.size - 2]!
  if F.getAppFn.isConstOf ``CategoryTheory.Functor.toPrefunctor then
    let a := F.getAppArgs
    F := headZeta a[a.size - 1]!
  unless F.getAppFn.isConstOf ``KltDP.Geometry.schemeModulePullback do
    throwError "Expected the original schemeModulePullback functor"
  let a := F.getAppArgs
  return (a[a.size - 1]!, args[args.size - 1]!)

private def homEndpoints (f : Expr) : MetaM (Expr × Expr) := do
  let args := (headZeta (← inferType f)).getAppArgs
  unless args.size ≥ 2 do throwError "Expected the original Hom endpoints"
  return (args[args.size - 2]!, args[args.size - 1]!)

private def nativeArguments (e h : Expr) : MetaM (Array (Name × Expr) × Level) := do
  let et := headZeta (← inferType e)
  unless et.isAppOfArity ``CategoryTheory.Iso 4 do throwError "Expected the original Iso"
  let ea := et.getAppArgs
  let (l, M) ← pullbackObjectParts ea[2]!
  let (_, N) ← pullbackObjectParts ea[3]!
  let (X, Y) ← homEndpoints l
  let ha ← equationArgs h
  let .const name levels := headZeta (← inferType X) |
    throwError "Expected an original scheme type"
  unless name == ``AlgebraicGeometry.Scheme && levels.length == 1 do
    throwError "Expected the original single scheme universe"
  return (#[(`X, X), (`Y, Y), (`l, l), (`l', ha[2]!), (`M, M), (`N, N),
    (`e, e), (`h, h)], levels[0]!)

private def explicitApplication (name : Name) (level : Level)
    (values : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo name
  unless info.levelParams.length == 1 do throwError "Unexpected generic universe count"
  let mut t := headZeta (info.type.instantiateLevelParams info.levelParams [level])
  let mut result := Lean.mkConst name [level]
  for _ in [:16] do
    match t with
    | .forallE binder _ body _ =>
      let some entry := values.find? (fun entry => entry.1 == binder) |
        throwError "Missing exact generic argument {binder}"
      result := mkApp result entry.2
      t := headZeta (body.instantiate1 entry.2)
    | _ => return result
  throwError "Generic application exceeded sixteen exact binders"

private def mappedMorphism (t : Expr) : MetaM Expr := do
  let t := headZeta t
  let .const name _ := t.getAppFn | throwError "Expected an original functor map"
  let args := t.getAppArgs
  unless name.toString.endsWith ".map" && !args.isEmpty do
    throwError "Expected an original functor-map application"
  return args[args.size - 1]!

elab "native_pullback_factor_iso%[" e:term "," h:term "]" : term => do
  let e ← elabTerm e none
  let h ← elabTerm h none
  synthesizeSyntheticMVarsNoPostponing
  let e ← unfoldNamedIso (← instantiateMVars e)
  let h ← instantiateMVars h
  let (args, level) ← nativeArguments e h
  explicitApplication ``KltDP.Geometry.SchemeModulePullbackMapEqFactor.nativeIso level args

elab "native_pullback_factor_comp%[" he:term "," h:term "]" : term => do
  let he ← elabTerm he none
  let h ← elabTerm h none
  synthesizeSyntheticMVarsNoPostponing
  let he ← instantiateMVars he
  let h ← instantiateMVars h
  let ha ← equationArgs he
  let lhs := (headZeta ha[1]!).getAppArgs
  unless lhs.size ≥ 2 do throwError "Expected the original normalized composite"
  let hom := headZeta lhs[lhs.size - 2]!
  unless hom.getAppFn.isConstOf ``CategoryTheory.Iso.hom do
    throwError "Expected the original factor Iso.hom"
  let e := hom.getAppArgs[hom.getAppArgs.size - 1]!
  let i ← mappedMorphism lhs[lhs.size - 1]!
  let m ← mappedMorphism ha[2]!
  let (_, T) ← homEndpoints i
  let (args, level) ← nativeArguments e h
  explicitApplication ``KltDP.Geometry.SchemeModulePullbackMapEqFactor.nativeIso_comp level
    (args ++ #[(`T, T), (`i, i), (`m, m), (`he, he)])

end KltDP.Geometry.SchemeModulePullbackNativeFactorTerm
