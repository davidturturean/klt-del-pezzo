import KltDP.Geometry.SingularClosed
import KltDP.Geometry.ClosedPoints

/-!
# Singular points of actual normal projective surfaces

Closedness of singular points and the canonical residue-field construction
give their residue fields over an algebraically closed base. Finiteness is
reduced to regular-locus openness, which remains an explicit required input
until its separate affine and literature adapters have been established.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The residue field of an actual singular point is isomorphic to the
algebraically closed base field through its canonical structure map. -/
def singularPoint_residueField_iso_base {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) : k ≃+* X.toScheme.residueField x :=
  closedPointResidueFieldEquiv X.structureMorphism x (singularPoint_isClosed X x hx)

/-- This is the original base-to-residue-field map, not merely an unrelated
isomorphism of the two underlying fields. -/
theorem singularPoint_residueField_iso_base_toRingHom
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) :
    (singularPoint_residueField_iso_base X x hx).toRingHom =
      (baseToResidueFieldMap X.structureMorphism x).hom := rfl

/-- The remaining openness theorem suffices for singular-locus finiteness.
Noetherianity and closedness of each singular point are derived from the
actual surface, rather than additional fields of its definition. -/
theorem normalSurface_singularLocus_finite_of_isOpen_regularLocus
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hopen : IsOpen (regularLocus X.toScheme)) :
    (singularLocus X.toScheme).Finite := by
  apply singularLocus_finite_of_isClosed_of_closedPoints X.toScheme
  · rw [singularLocus_eq_compl_regularLocus]
    exact hopen.isClosed_compl
  · exact fun x hx => singularPoint_isClosed X x hx

end KltDP.Geometry
