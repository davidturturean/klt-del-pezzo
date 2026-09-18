import KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquareCarriers
import KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquareCarriers

/-!
# Align only the four proof annotations measured in the original source square

The source transition and the local transition have identical native data.
Transport the cached source proposition through its four proof arguments,
using an arbitrary proposition family; no scheme-valued conversion lemma is
instantiated. The generated term uses only the generic theorem below.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Lean Meta Elab Term
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations

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
    throwError "source proof annotations: unexpected {label} head/arity"
  return e.getAppArgs

private def atPath (e : Expr) (path : Array Nat) : MetaM Expr := do
  let mut current := e
  for i in path do
    let arguments := (headZeta current).getAppArgs
    unless i < arguments.size do
      throwError "source proof annotations: measured argument path changed"
    current := arguments[i]!
  return headZeta current

/-- Read the proof binder of the literal enclosing native application. -/
private def proofDomain (source : Expr) (path : Array Nat) : MetaM Expr := do
  let application ← atPath source (path.extract 0 (path.size - 1))
  let index := path[path.size - 1]!
  let .const name levels := application.getAppFn
    | throwError "source proof annotations: expected a native constant application"
  let info ← getConstInfo name
  let mut ty := info.type.instantiateLevelParams info.levelParams levels
  let arguments := application.getAppArgs
  for i in [:index] do
    let .forallE _ _ body _ := headZeta ty
      | throwError "source proof annotations: missing preceding native binder"
    ty := body.instantiate1 arguments[i]!
  let .forallE _ domain _ _ := headZeta ty
    | throwError "source proof annotations: missing native proof binder"
  unless ← isProp domain do
    throwError "source proof annotations: measured argument is not a proof"
  return domain

elab "align_source_annotations% " hs:term " with " ha:term : term => do
  let sourceProof ← elabTerm hs none
  let localProof ← elabTerm ha none
  let mut sourceType := headZeta (← inferType sourceProof)
  let sourceEq ← requireArgs "source equation" sourceType ``Eq 3
  let localEq ← requireArgs "local equation" (← inferType localProof) ``Eq 3
  let sourceLeft ← requireArgs "source left" sourceEq[1]!
    ``CategoryTheory.CategoryStruct.comp 7
  let localRight ← requireArgs "local right" localEq[2]!
    ``CategoryTheory.CategoryStruct.comp 7
  let mut sourceArrow := headZeta sourceLeft[6]!
  let localArrow := headZeta localRight[5]!
  let mut result := sourceProof
  -- These are exactly the four complete, untruncated U681 differences.
  let paths : Array (Array Nat) := #[
    #[2, 4, 4, 2, 2, 4, 6], #[2, 4, 4, 2, 2, 4, 7],
    #[4, 5, 6], #[4, 6, 4]]
  for path in paths do
    let oldProof ← atPath sourceArrow path
    let newProof ← atPath localArrow path
    let domain ← proofDomain sourceArrow path
    let previousResult := result
    let previousType := sourceType
    let transported ← withLocalDeclD `proofParameter domain fun parameter => do
      let body := previousType.replace fun e =>
        if e == oldProof then some parameter else none
      let family ← mkLambdaFVars #[parameter] body
      mkAppOptM ``replace_proof #[some domain, some family, some oldProof,
        some previousResult, some newProof]
    result := transported
    sourceType := sourceType.replace fun e =>
      if e == oldProof then some newProof else none
    sourceArrow := sourceArrow.replace fun e =>
      if e == oldProof then some newProof else none
  return result

/-- The original source equation with only its proof annotations aligned to the local one. -/
def source_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    align_source_annotations%
      (GluedAdjunctionIntrinsicSourceSquareCarriers.source_square f I U r) with
      (GluedAdjunctionIntrinsicLocalSquareCarriers.local_square f I U r d hU hd hAmbient hCurve)

end KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations
