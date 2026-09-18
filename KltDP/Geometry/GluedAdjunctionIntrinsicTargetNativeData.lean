import KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations

/-!
# Exact native data reductions in the final target comparison

U747 classified the measured nodes as data rather than proof arguments.
Reduce literal ModuleCat.of projections to their stored fields and the
known functor/ring projections in a copy of the native proposition. A typed
let reuses the cached original proof; the kernel checks every definitional
conversion. No target morphism or abstract compatibility is introduced.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Lean Meta Elab Term
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData

private partial def headZeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | e => e.headBeta

private def args (label : String) (e : Expr) (head : Name) (count : Nat) :
    MetaM (Array Expr) := do
  let e := headZeta e
  unless e.getAppFn.constName? == some head && e.getAppArgs.size == count do
    throwError "target native data: unexpected {label} head/arity"
  return e.getAppArgs

private def atPath (e : Expr) (path : Array Nat) : MetaM Expr := do
  let mut current := e
  for index in path do
    let arguments := (headZeta current).getAppArgs
    unless index < arguments.size do
      throwError "target native data: measured path changed"
    current := arguments[index]!
  return headZeta current

private def typedProofCopy (proof proposition : Expr)
    (replacements : Array (Expr × Expr)) : MetaM Expr := do
  let normalized := proposition.replace fun expression =>
    (replacements.find? (fun pair => pair.1 == expression)).map Prod.snd
  if normalized == proposition then
    throwError "target native data: no recorded projection occurrence changed"
  return .letE `normalizedOriginalProof normalized proof (.bvar 0) false

elab "target_native_data% " h:term : term => do
  let proof ← elabTerm h none
  let proposition := headZeta (← inferType proof)
  let equation ← args "target equation" proposition ``Eq 3
  let right ← args "target right" equation[2]! ``CategoryTheory.CategoryStruct.comp 7
  let tail ← args "target tail" right[6]! ``CategoryTheory.CategoryStruct.comp 7
  let transition := mkAppN (headZeta equation[2]!).getAppFn
    #[right[0]!, right[1]!, right[2]!, right[3]!, tail[3]!, right[5]!, tail[5]!]
  let paths : Array (Array Nat) := #[
    #[5, 4, 3, 5, 2, 3, 3, 1, 5, 0, 1],
    #[5, 4, 3, 5, 2, 3, 3, 1, 5, 0, 3, 1],
    #[5, 4, 3, 5, 2, 3, 3, 1, 5, 0, 4]]
  let heads := #[``ModuleCat.carrier, ``ModuleCat.isAddCommGroup, ``ModuleCat.isModule]
  let mut replacements : Array (Expr × Expr) := #[]
  for index in [:3] do
    let original ← atPath transition paths[index]!
    let projection ← args "module projection" original heads[index]! 3
    let bundled ← args "literal module bundle" projection[2]! ``ModuleCat.of 5
    replacements := replacements.push (original, bundled[index + 2]!)
  let originalSemiring ← atPath transition #[5, 4, 3, 5, 2, 4, 2]
  let ring ← args "ring semiring projection" originalSemiring ``Ring.toSemiring 2
  let commRing ← args "commutative ring projection" ring[1]! ``CommRing.toRing 2
  let commSemiring ← mkAppOptM ``CommRing.toCommSemiring
    #[some commRing[0]!, some commRing[1]!]
  let normalizedSemiring ← mkAppOptM ``CommSemiring.toSemiring
    #[some commRing[0]!, some commSemiring]
  replacements := replacements.push (originalSemiring, normalizedSemiring)
  typedProofCopy proof proposition replacements

elab "local_native_data% " h:term : term => do
  let proof ← elabTerm h none
  let proposition := headZeta (← inferType proof)
  let equation ← args "local equation" proposition ``Eq 3
  let left ← args "local left" equation[1]! ``CategoryTheory.CategoryStruct.comp 7
  let original ← atPath left[6]! #[5, 4, 3, 0, 0, 0, 1, 0]
  let projection := original.getAppArgs
  unless original.getAppFn.constName? == some ``Prefunctor.obj && projection.size >= 5 do
    throwError "target native data: expected Prefunctor.obj with its four parameters and self, argc={projection.size}"
  let normalized := mkAppN (Expr.proj ``Prefunctor 0 projection[4]!)
    (projection.extract 5 projection.size)
  typedProofCopy proof proposition #[(original, normalized)]

/-- The original target square with exactly the measured native data projections reduced. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    target_native_data%
      (GluedAdjunctionIntrinsicTargetProofAnnotations.target_square f I hI U r d hU hd hAmbient hCurve)

/-- The same local square with the literal prefunctor object projection reduced. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    local_native_data%
      (GluedAdjunctionIntrinsicTargetModuleProjections.local_square f I U r d hU hd hAmbient hCurve)

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData
