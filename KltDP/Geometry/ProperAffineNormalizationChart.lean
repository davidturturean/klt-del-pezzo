import KltDP.Geometry.ProperAffineIntegralClosure

/-!
# The original integral-closure spectrum on a proper affine chart

The chart is the spectrum of the actual integral-closure subalgebra.
Its comparison with the spectrum of original global functions is induced
by the original inclusion, and commutes with the original base maps.
No independent replacement algebra or target is introduced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperAffineSections

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- The actual integral-closure spectrum on the original affine chart. -/
def normalizationChart : Scheme.{u} :=
  letI := (baseScalar f).toAlgebra
  Spec (CommRingCat.of (integralClosure R Γ(X, ⊤)))

/-- Its original structure map to the affine base. -/
def normalizationChartToBase : normalizationChart f ⟶ Spec (CommRingCat.of R) := by
  letI := (baseScalar f).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Γ(X, ⊤))))

/-- The map induced by the literal integral-closure inclusion into the section ring. -/
def toNormalizationChart : Spec Γ(X, ⊤) ⟶ normalizationChart f := by
  letI := (baseScalar f).toAlgebra
  exact Spec.map (CommRingCat.ofHom (integralClosure R Γ(X, ⊤)).val.toRingHom)

/-- The proved integral-closure equality makes this original inclusion invertible. -/
def normalizationChartIso : Spec Γ(X, ⊤) ≅ normalizationChart f := by
  letI := (baseScalar f).toAlgebra
  exact Scheme.Spec.mapIso (integralClosureEquiv f).toRingEquiv.toCommRingCatIso.op

@[simp] theorem normalizationChartIso_hom :
    (normalizationChartIso f).hom = toNormalizationChart f := rfl

/-- The comparison retains exactly the original affine-base scalar map. -/
@[reassoc] theorem toNormalizationChart_toBase :
    toNormalizationChart f ≫ normalizationChartToBase f = toSpecBase f := by
  letI := (baseScalar f).toAlgebra
  change Spec.map (CommRingCat.ofHom (integralClosure R Γ(X, ⊤)).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Γ(X, ⊤)))) =
      Spec.map (CommRingCat.ofHom (baseScalar f))
  rw [← Spec.map_comp]
  congr 1

/-- The original affinization map gives the original normalization-chart factorization. -/
theorem toSpecΓ_toNormalizationChart_toBase :
    X.toSpecΓ ≫ toNormalizationChart f ≫ normalizationChartToBase f = f := by
  rw [toNormalizationChart_toBase, toSpecΓ_toSpecBase]

end KltDP.Geometry.ProperAffineSections
