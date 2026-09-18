import KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData

/-!
# Keep the original section-ring presentation in the target square

The native projection reduction is made on the target equation only. Its
prefunctor and every trailing argument must be literally those of the cached
local equation. A typed copy retains the original proof and checks the sole
projection conversion in the kernel; no diagram morphism is replaced.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Lean Meta Elab Term
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor

private partial def headZeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | e => e.headBeta

private def args (label : String) (e : Expr) (head : Name) (count : Nat) :
    MetaM (Array Expr) := do
  let e := headZeta e
  unless e.getAppFn.constName? == some head && e.getAppArgs.size == count do
    throwError "target original prefunctor: unexpected {label} head/arity"
  return e.getAppArgs

private def atPath (e : Expr) (path : Array Nat) : MetaM Expr := do
  let mut current := e
  for index in path do
    let arguments := (headZeta current).getAppArgs
    unless index < arguments.size do
      throwError "target original prefunctor: measured path changed"
    current := arguments[index]!
  return headZeta current

elab "target_original_prefunctor% " h:term " using " reference:term : term => do
  let rawProof ← elabTerm h none
  let rawLocal ← elabTerm reference none
  let proof ← instantiateMVars rawProof
  let cachedLocal ← instantiateMVars rawLocal
  let proposition := headZeta (← instantiateMVars (← inferType proof))
  let equation ← args "target equation" proposition ``Eq 3
  let right ← args "target right" equation[2]! ``CategoryTheory.CategoryStruct.comp 7
  let tail ← args "target tail" right[6]! ``CategoryTheory.CategoryStruct.comp 7
  let transition := mkAppN (headZeta equation[2]!).getAppFn
    #[right[0]!, right[1]!, right[2]!, right[3]!, tail[3]!, right[5]!, tail[5]!]
  let localEquation ← args "local equation"
    (← instantiateMVars (← inferType cachedLocal)) ``Eq 3
  let left ← args "local left" localEquation[1]! ``CategoryTheory.CategoryStruct.comp 7
  let path := #[5, 4, 3, 0, 0, 0, 1, 0]
  let projected ← instantiateMVars (← atPath transition path)
  let original ← instantiateMVars (← atPath left[6]! path)
  let originalArgs := original.getAppArgs
  unless original.getAppFn.constName? == some ``Prefunctor.obj && originalArgs.size >= 5 do
    throwError "target original prefunctor: expected the original object projection"
  let .proj ``Prefunctor 0 self := projected.getAppFn |
    throwError "target original prefunctor: expected native field projection zero"
  unless headZeta self == headZeta originalArgs[4]! do
    throwError "target original prefunctor: native prefunctor data differ"
  unless projected.getAppArgs == originalArgs.extract 5 originalArgs.size do
    throwError "target original prefunctor: trailing object arguments differ"
  let normalized := proposition.replace fun expression =>
    if expression == projected then some original else none
  if normalized == proposition then
    throwError "target original prefunctor: no recorded occurrence changed"
  return .letE `originalTargetProof normalized proof (.bvar 0) false

/-- The original target equation in the unchanged local diagram's section-ring presentation. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    target_original_prefunctor%
      (GluedAdjunctionIntrinsicTargetNativeData.target_square f I hI U r d hU hd hAmbient hCurve)
      using
      (GluedAdjunctionIntrinsicTargetModuleProjections.local_square f I U r d hU hd hAmbient hCurve)

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor
