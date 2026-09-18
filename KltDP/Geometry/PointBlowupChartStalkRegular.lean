import KltDP.Geometry.SchemePointBlowupSourceRegular
import KltDP.Geometry.SchemePointBlowupSequenceProper

/-! Regularity and dimension of the original closed-point blowup chart stalks. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every closed point of an actual affine chart of an original point-blowup
source has a regular local ring of dimension two. -/
theorem SchemePointBlowup.IsAt.affineChart_stalk_regular_dimension
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {S : Scheme.{u}} {f : S ⟶ X.toScheme} {x : X.toScheme} (h : SchemePointBlowup.IsAt f x)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ S) [IsOpenImmersion j]
    (P : Ideal A) [P.IsMaximal] :
    RegularLocal (Localization.AtPrime P) ∧ ringKrullDim (Localization.AtPrime P) = 2 := by
  letI : IsIntegral S := h.source_isIntegral_of_surface X
  letI : IsLocallyNoetherian X.toScheme :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec X.structureMorphism
  letI : IsProper f := h.isProper
  letI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace (f ≫ X.structureMorphism)
  let p : PrimeSpectrum A := ⟨P, inferInstance⟩
  have hclosed : IsClosed ({j.base p} : Set S) := by
    change p ∈ j.base ⁻¹' closedPoints S
    rw [j.isOpenEmbedding.preimage_closedPoints]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr inferInstance
  let e := openImmersionStalkLocalizationEquiv j p
  refine ⟨regularLocal_of_ringEquiv e (h.source_regular X (j.base p)), ?_⟩
  exact (ringKrullDim_eq_of_ringEquiv e).symm.trans
    ((closed_stalk_dimension_eq_global S (f ≫ X.structureMorphism) (j.base p) hclosed).trans
      (h.source_dimension_two X))

namespace NormalProjectiveSurface

/-- This applies the preceding theorem to the literal Rees chart and its
original open inclusion into the original glued blowup. -/
theorem pointBlowup_chart_stalk_regular_dimension
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme)) (a : q.asIdeal)
    (P : Ideal (AffineBlowup.chartRing q.asIdeal a)) [P.IsMaximal] :
    RegularLocal (Localization.AtPrime P) ∧ ringKrullDim (Localization.AtPrime P) = 2 := by
  let c : PointBlowupChart X.toScheme (j.base q) :=
    { R := R, j := j, q := q, isClosed := hclosed, base_eq := rfl }
  exact (SchemePointBlowup.isAt_projection c).affineChart_stalk_regular_dimension X
    (AffineBlowup.chartι q.asIdeal a ≫ PointBlowupGluing.affineBlowupι j q hclosed) P

end NormalProjectiveSurface

end KltDP.Geometry
