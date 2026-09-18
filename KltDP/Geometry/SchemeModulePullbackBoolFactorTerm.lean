import KltDP.Geometry.SchemeModulePullbackBoolFactor
import Lean

/-!
# Explicit applications of the proved Boolean pullback-factor assembly

Each of the eight or thirteen supplied arguments is elaborated independently.
The result is an ordinary fully specified application of the generic proved
constructor or theorem. Its remaining argument is the original chart index.
The kernel checks every carrier and equation; no conversion search or stored
geometric proof is unfolded by this term elaborator.
-/

open Lean Meta Elab Term

namespace KltDP.Geometry.SchemeModulePullbackBoolFactorTerm

private def explicitApplication (name : Name) (ts : Array (TSyntax `term)) : TermElabM Expr := do
  let args ← ts.mapM (fun t => elabTerm t none)
  synthesizeSyntheticMVarsNoPostponing
  let args ← args.mapM instantiateMVars
  let .const schemeName levels := (← inferType args[0]!).consumeMData.headBeta |
    throwError "Expected the original target scheme type"
  unless schemeName == ``AlgebraicGeometry.Scheme && levels.length == 1 do
    throwError "Expected the original single scheme universe"
  let info ← getConstInfo name
  unless info.levelParams.length == 1 do throwError "Unexpected generic universe count"
  return mkAppN (Lean.mkConst name [levels[0]!]) args

elab "bool_pullback_factor_iso%[" Y:term "," P:term "," Z:term "," l:term ","
    M:term "," N:term "," e0:term "," e1:term "]" : term =>
  explicitApplication ``KltDP.Geometry.SchemeModulePullbackBoolFactor.iso
    #[Y, P, Z, l, M, N, e0, e1]

elab "bool_pullback_factor_comp%[" Y:term "," P:term "," Z:term "," l:term ","
    M:term "," N:term "," T:term "," e0:term "," e1:term "," i:term "," m:term ","
    h0:term "," h1:term "]" : term =>
  explicitApplication ``KltDP.Geometry.SchemeModulePullbackBoolFactor.iso_comp
    #[Y, P, Z, l, M, N, T, e0, e1, i, m, h0, h1]

end KltDP.Geometry.SchemeModulePullbackBoolFactorTerm
