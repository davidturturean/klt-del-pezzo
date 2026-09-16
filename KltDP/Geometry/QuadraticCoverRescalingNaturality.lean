import KltDP.Geometry.QuadraticCoverRestriction

/-!
# Restriction commutes with actual quadratic generator changes

The coefficient map between the actual quadratic quotients commutes with
rescaling the root, with the unit mapped through the original coefficient
homomorphism. Passing to spectra gives the actual square in both directions.
These are the restriction squares needed to combine the proved transition
cocycle on common opens with scheme gluing on an arbitrary affine atlas.

The proof reuses pinned `AdjoinRoot.algHom_ext`, `AlgHom.restrictScalars`,
and the already constructed coefficient and rescaling maps. No quotient
identification, naturality square, or global glued cover is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The literal branch equation is preserved by the original coefficient map. -/
theorem rescaleCondition_algebraMap (s s' v : R) (h : s = v ^ 2 * s') :
    algebraMap R S s = algebraMap R S v ^ 2 * algebraMap R S s' := by
  rw [h, map_mul, map_pow]

/-- The two actual quotient homomorphisms commute on every element, proved
by their base scalars and the adjoined root. -/
theorem baseChangeCoeffHom_rescaleHom (s s' v : R) (h : s = v ^ 2 * s') :
    (baseChangeCoeffHom (S := S) s').comp (rescaleHom s s' v h) =
      ((rescaleHom (algebraMap R S s) (algebraMap R S s') (algebraMap R S v)
        (rescaleCondition_algebraMap (S := S) s s' v h)).restrictScalars R).comp
        (baseChangeCoeffHom (S := S) s) := by
  apply AdjoinRoot.algHom_ext
  change baseChangeCoeffHom (S := S) s' (rescaleHom s s' v h (root s)) =
    rescaleHom (algebraMap R S s) (algebraMap R S s') (algebraMap R S v)
      (rescaleCondition_algebraMap (S := S) s s' v h)
      (baseChangeCoeffHom (S := S) s (root s))
  simp only [rescaleHom_root, baseChangeCoeffHom_root, map_mul,
    baseChangeCoeffHom_algebraMap]

/-- Unit generator changes commute with the actual coefficient map; the new
transition is the mapped original unit. -/
theorem baseChangeCoeffHom_rescaleEquiv (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') (x : CoverAlgebra s) :
    baseChangeCoeffHom (S := S) s' (rescaleEquiv s s' v h x) =
      rescaleEquiv (algebraMap R S s) (algebraMap R S s')
        (Units.map (algebraMap R S).toMonoidHom v)
        (rescaleCondition_algebraMap (S := S) s s' (v : R) h)
        (baseChangeCoeffHom (S := S) s x) :=
  AlgHom.congr_fun (baseChangeCoeffHom_rescaleHom (S := S) s s' (v : R) h) x

/-- The actual restriction and generator-change maps commute on spectra. -/
@[reassoc]
theorem baseChangeProjection_rescaleSpecIso_hom (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') :
    baseChangeProjection (S := S) s' ≫ (rescaleSpecIso s s' v h).hom =
      (rescaleSpecIso (algebraMap R S s) (algebraMap R S s')
        (Units.map (algebraMap R S).toMonoidHom v)
        (rescaleCondition_algebraMap (S := S) s s' (v : R) h)).hom ≫
        baseChangeProjection (S := S) s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact baseChangeCoeffHom_rescaleEquiv (S := S) s s' v h x

/-- The inverse generator-change square is derived from the proved forward
square, retaining the original coefficient maps. -/
@[reassoc]
theorem baseChangeProjection_rescaleSpecIso_inv (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') :
    baseChangeProjection (S := S) s ≫ (rescaleSpecIso s s' v h).inv =
      (rescaleSpecIso (algebraMap R S s) (algebraMap R S s')
        (Units.map (algebraMap R S).toMonoidHom v)
        (rescaleCondition_algebraMap (S := S) s s' (v : R) h)).inv ≫
        baseChangeProjection (S := S) s' := by
  apply (cancel_mono (rescaleSpecIso s s' v h).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [baseChangeProjection_rescaleSpecIso_hom, Iso.inv_hom_id_assoc]

end KltDP.Geometry.QuadraticCover
