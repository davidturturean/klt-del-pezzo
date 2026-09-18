import KltDP.Geometry.AdjunctionRefinementComponentNormalization
import KltDP.Geometry.GluedAdjunctionChartBasis
import KltDP.Geometry.GluedAdjunctionIntrinsicChartRefinement
import KltDP.Geometry.GluedAdjunctionCommonRefinementOriginalMaps

/-!
# Retain both original object-equality proofs in the normalized chart equation

The actual intrinsic square fixes the native categories and chart arrows.
The cached original map expansion supplies its literal source and target
object-equality proofs. Normalize those proof annotations abstractly before
returning the native equation; no original map or hypothesis is replaced.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Lean Meta Elab Term
universe u
namespace KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization
open GluedAdjunctionChartBasis

private partial def headZeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | e => e.headBeta

private def args (label : String) (e : Expr) (head : Name) (count : Nat) :
    MetaM (Array Expr) := do
  let e := headZeta e
  unless e.getAppFn.constName? == some head && e.getAppArgs.size == count do
    throwError "native component normalization: {label} has head {e.getAppFn.constName?}, argc={e.getAppArgs.size}"
  return e.getAppArgs

private def equationType (type : Expr) : MetaM Expr := do
  let mut current := headZeta type
  for _ in [:3] do
    if current.getAppFn.constName? == some ``Eq then return current
    let .const name _ := current.getAppFn |
      throwError "native component normalization: expected equation wrapper"
    let arguments := current.getAppArgs
    unless name.toString.endsWith ".statementOf" && arguments.size == 2 do
      throwError "native component normalization: unexpected equation wrapper {name}"
    current := headZeta arguments[0]!
  throwError "native component normalization: equation wrapper depth exceeded"

private def homIso (e : Expr) : MetaM Expr := do
  let e := headZeta e
  match e.getAppFn with
  | .proj ``CategoryTheory.Iso 0 value => return value
  | _ => return (← args "isomorphism hom" e ``CategoryTheory.Iso.hom 5)[4]!

private def transportProof (e : Expr) : MetaM Expr := do
  let e := headZeta e
  if e.getAppFn.constName? == some ``CategoryTheory.eqToHom then
    return (← args "equality transport" e ``CategoryTheory.eqToHom 5)[4]!
  let value ← homIso e
  return (← args "equality isomorphism" value ``CategoryTheory.eqToIso 5)[4]!

elab "original_component_normalization% " h:term " using " original:term : term => do
  let rawProof ← elabTerm h none
  let rawOriginal ← elabTerm original none
  let proof ← instantiateMVars rawProof
  let originalProof ← instantiateMVars rawOriginal
  let proposition ← equationType (← instantiateMVars (← inferType proof))
  let equation ← args "equation" proposition ``Eq 3
  let left ← args "left composite" equation[1]! ``CategoryTheory.CategoryStruct.comp 7
  let right ← args "right composite" equation[2]! ``CategoryTheory.CategoryStruct.comp 7
  let source ← args "source comparison" right[5]! ``CategoryTheory.CategoryStruct.comp 7
  let target ← args "target comparison" left[6]! ``CategoryTheory.CategoryStruct.comp 7
  let sourceFirst ← args "source component" source[5]! ``CategoryTheory.NatTrans.app 8
  let targetFirst ← args "target component" target[5]! ``CategoryTheory.NatTrans.app 8
  let targetSecond ← args "target transport" target[6]! ``CategoryTheory.NatTrans.app 8
  let originalIso ← homIso sourceFirst[6]!
  let originalSourceEquality ← transportProof source[6]!
  let originalEquality ← transportProof targetSecond[6]!
  let originalType ← equationType (← instantiateMVars (← inferType originalProof))
  let originalEq ← args "original expansion equation" originalType ``Eq 3
  let originalLeft ← args "original expansion left" originalEq[1]!
    ``CategoryTheory.CategoryStruct.comp 7
  let originalTail ← args "original expansion tail" originalLeft[6]!
    ``CategoryTheory.CategoryStruct.comp 7
  let inverse ← args "original source inverse" originalLeft[5]! ``CategoryTheory.Iso.inv 5
  let sourceIso ← args "original source isomorphism" inverse[4]! ``CategoryTheory.Iso.trans 7
  let targetIso ← args "original target isomorphism"
    (← homIso originalTail[6]!) ``CategoryTheory.Iso.trans 7
  let sourceObject ← args "original source object equality" sourceIso[6]!
    ``CategoryTheory.eqToIso 5
  let targetObject ← args "original target object equality" targetIso[6]!
    ``CategoryTheory.eqToIso 5
  mkAppOptM ``AdjunctionRefinementComponentNormalization.original_object_square
    #[some sourceFirst[0]!, some sourceFirst[2]!, some sourceFirst[1]!,
      some sourceFirst[3]!, some sourceFirst[4]!, some sourceFirst[5]!,
      some targetSecond[5]!, some originalIso, some originalEquality,
      some sourceFirst[7]!, some targetFirst[7]!, some originalSourceEquality,
      some sourceObject[4]!, some targetObject[4]!, some left[5]!,
      some right[6]!, some proof]

/-- Normalize the proved original intrinsic square on an actual simultaneous chart. -/
def chart_square {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (c : Chart f I) (r : Γ(X, c.U.1)) :=
  letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, c.U.1) ⧸ I.ideal c.U) := c.curve
  original_component_normalization%
    (GluedAdjunctionIntrinsicChartRefinement.iso_refinement f I hI c.U r c.d c.equation c.regular)
    using (GluedAdjunctionCommonRefinementOriginalMaps.refinedHom_expansion f I hI c r)

end KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization
