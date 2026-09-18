import KltDP.Geometry.GluedAdjunctionIntrinsicTargetModuleProjections

/-!
# Align the measured proof annotations in the original target transition

The cached target proposition is transported through exactly the two
IsTwoSided arguments and the differential-module SMulCommClass argument
reported in U709. All target maps and native module carriers are retained.
The term uses the same generic proposition-family proof as the compiled
source annotation repair, with no scheme-specific equality conversion.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Lean Meta Elab Term
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations

private theorem replace_proof {P : Prop} (F : P → Prop) (old : P)
    (h : F old) (new : P) : F new :=
  Eq.mp (congrArg F (Subsingleton.elim old new)) h

private partial def headZeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | e => e.headBeta

private def requireArgs (label : String) (e : Expr) (head : Name) (count : Nat) :
    MetaM (Array Expr) := do
  let e := headZeta e
  unless e.getAppFn.constName? == some head && e.getAppArgs.size == count do
    throwError "target proof annotations: unexpected {label} head/arity"
  return e.getAppArgs

private def atPath (e : Expr) (path : Array Nat) : MetaM Expr := do
  let mut current := e
  for i in path do
    let arguments := (headZeta current).getAppArgs
    unless i < arguments.size do
      throwError "target proof annotations: measured argument path changed"
    current := arguments[i]!
  return headZeta current

/-- Read the proof binder of the literal enclosing native application. -/
private def proofDomain (source : Expr) (path : Array Nat) : MetaM Expr := do
  let application ← atPath source (path.extract 0 (path.size - 1))
  let index := path[path.size - 1]!
  let .const name levels := application.getAppFn
    | throwError "target proof annotations: expected a native constant application"
  let info ← getConstInfo name
  let mut ty := info.type.instantiateLevelParams info.levelParams levels
  let arguments := application.getAppArgs
  for i in [:index] do
    let .forallE _ _ body _ := headZeta ty
      | throwError "target proof annotations: missing preceding native binder"
    ty := body.instantiate1 arguments[i]!
  let .forallE _ domain _ _ := headZeta ty
    | throwError "target proof annotations: missing native proof binder"
  unless ← isProp domain do
    throwError "target proof annotations: measured argument is not a proof"
  return domain

elab "align_target_annotations% " hc:term " with " ha:term : term => do
  let targetProof ← elabTerm hc none
  let localProof ← elabTerm ha none
  let mut targetType := headZeta (← inferType targetProof)
  let targetEq ← requireArgs "target equation" targetType ``Eq 3
  let localEq ← requireArgs "local equation" (← inferType localProof) ``Eq 3
  let targetRight ← requireArgs "target right" targetEq[2]!
    ``CategoryTheory.CategoryStruct.comp 7
  let targetTail ← requireArgs "target final factors" targetRight[6]!
    ``CategoryTheory.CategoryStruct.comp 7
  let localLeft ← requireArgs "local left" localEq[1]!
    ``CategoryTheory.CategoryStruct.comp 7
  let mut targetArrow := mkAppN (headZeta targetEq[2]!).getAppFn
    #[targetRight[0]!, targetRight[1]!, targetRight[2]!, targetRight[3]!,
      targetTail[3]!, targetRight[5]!, targetTail[5]!]
  let localArrow := headZeta localLeft[6]!
  let mut result := targetProof
  -- Only these three proof positions, not the remaining truncated data comparison.
  let paths : Array (Array Nat) := #[
    #[2, 4, 4, 2, 2, 4, 6], #[2, 4, 4, 2, 2, 4, 7],
    #[2, 5, 3, 5, 2, 2, 0, 4, 8]]
  for path in paths do
    let oldProof ← atPath targetArrow path
    let newProof ← atPath localArrow path
    let domain ← proofDomain targetArrow path
    let previousResult := result
    let previousType := targetType
    let transported ← withLocalDeclD `proofParameter domain fun parameter => do
      let body := previousType.replace fun e =>
        if e == oldProof then some parameter else none
      let family ← mkLambdaFVars #[parameter] body
      mkAppOptM ``replace_proof #[some domain, some family, some oldProof,
        some previousResult, some newProof]
    result := transported
    targetType := targetType.replace fun e =>
      if e == oldProof then some newProof else none
    targetArrow := targetArrow.replace fun e =>
      if e == oldProof then some newProof else none
  return result

/-- The original target equation with only its measured proof annotations aligned. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    align_target_annotations%
      (GluedAdjunctionIntrinsicTargetModuleProjections.target_square
        f I hI U r d hU hd hAmbient) with
      (GluedAdjunctionIntrinsicTargetModuleProjections.local_square
        f I U r d hU hd hAmbient hCurve)

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations
