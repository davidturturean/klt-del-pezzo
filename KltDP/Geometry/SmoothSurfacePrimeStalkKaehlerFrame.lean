import KltDP.Geometry.SmoothSurfaceStalkKaehlerBasis
import KltDP.Geometry.SmoothSurfaceRelativeDimension
import KltDP.Geometry.PrimeDivisor

/-!
# Native determinant evaluation at an original source prime

For the original smooth normal projective surface, relative dimension two
is derived by the compiled surface theorem. Specialize the native stalk
frame at the actual generic point of the given prime curve.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [hSmooth : IsSmooth S.structureMorphism] (C : S.PrimeCurve)

include hSmooth

/-- A basis on the literal ambient stalk at the original prime generic point. -/
def nativeKaehlerBasis :
    letI := stalkAlgebra S.structureMorphism C.genericPoint
    Basis (Fin 2) (S.stalk C.genericPoint) (KaehlerDifferential k (S.stalk C.genericPoint)) := by
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  letI := S.isSmoothOfRelativeDimension_two
  exact SmoothSurfaceStalkKaehlerBasis.basis S.structureMorphism C.genericPoint

/-- Its native determinant gives a scalar evaluator with an actual inverse. -/
def nativeKaehlerDeterminant :
    letI := stalkAlgebra S.structureMorphism C.genericPoint
    (⋀[(S.stalk C.genericPoint)]^2 (KaehlerDifferential k (S.stalk C.genericPoint))) ≃ₗ[S.stalk C.genericPoint]
      S.stalk C.genericPoint := by
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  exact AffineTopDifferentialFrame.determinantEquiv (nativeKaehlerBasis S C)

/-- The evaluator sends the actual native basis wedge to one. -/
theorem nativeKaehlerDeterminant_basis_wedge :
    letI := stalkAlgebra S.structureMorphism C.genericPoint
    nativeKaehlerDeterminant S C
      (exteriorPower.ιMulti (S.stalk C.genericPoint) 2 (nativeKaehlerBasis S C)) = 1 := by
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  exact AffineTopDifferentialFrame.determinantEquiv_basis_wedge (nativeKaehlerBasis S C)

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
