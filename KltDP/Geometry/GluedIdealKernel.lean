import KltDP.Geometry.PrimeCurveSubscheme

/-!
# The affine kernels of an actual glued ideal subscheme

The quotient-chart gluing and its inclusion are the actual objects already
constructed in `PrimeCurveSubscheme`. The chart isomorphism transports the
pinned quotient-map kernel calculation to the actual restricted inclusion.
In particular, no equality of a constructed kernel with the original
ideal is supplied as a hypothesis.

The `topIso` comap is retained explicitly: its source is sections of the
affine open as a scheme, whereas the original ideal is in the ambient
scheme's sections on that open. The global equality of ideal sheaves and
the corresponding module-sheaf trivializations are separate adapters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual sections of the restricted closed subscheme are the
quotient of the ambient affine section ring by the original ideal. -/
def gluedRestrictionSectionsIso (U : X.affineOpens) :
    Γ((I.gluedTo ⁻¹ᵁ U.1).toScheme, ⊤) ≅
      CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U) :=
  asIso (I.glueDataObjIso U).hom.appTop ≪≫ Scheme.ΓSpecIso _

/-- Under the actual chart isomorphism, the structural section map is
the canonical quotient map after the canonical affine section transport. -/
theorem gluedTo_restrict_appTop_comp_sectionsIso (U : X.affineOpens) :
    (I.gluedTo ∣_ U.1).appTop ≫ (I.gluedRestrictionSectionsIso U).hom =
      U.1.topIso.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) := by
  change (I.gluedTo ∣_ U.1).appTop ≫
      ((I.glueDataObjIso U).hom.appTop ≫ (Scheme.ΓSpecIso _).hom) = _
  rw [← Category.assoc, ← Scheme.comp_appTop, I.glueDataObjIso_hom_restrict U,
    glueDataObjι, Scheme.comp_appTop, U.2.isoSpec_inv_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The actual inclusion restricted to an affine open has precisely the
kernel of the original ideal, with its canonical section-ring transport. -/
theorem ker_gluedTo_restrict_appTop (U : X.affineOpens) :
    RingHom.ker (I.gluedTo ∣_ U.1).appTop.hom =
      (I.ideal U).comap U.1.topIso.hom.hom := by
  have h := congrArg (fun f : I.glueDataObj U ⟶ U.1.toScheme => f.appTop)
    (I.glueDataObjIso_hom_restrict U)
  have hinj : Function.Injective (I.glueDataObjIso U).hom.appTop.hom :=
    (asIso (I.glueDataObjIso U).hom.appTop).commRingCatIsoToRingEquiv.injective
  calc
    RingHom.ker (I.gluedTo ∣_ U.1).appTop.hom =
        RingHom.ker ((I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ U.1).appTop.hom := by
      simpa only [Scheme.comp_appTop, CommRingCat.hom_comp] using
        (RingHom.ker_comp_of_injective (I.gluedTo ∣_ U.1).appTop.hom hinj).symm
    _ = RingHom.ker (I.glueDataObjι U).appTop.hom := congrArg (fun f => RingHom.ker f.hom) h
    _ = (I.ideal U).comap U.1.topIso.hom.hom := I.ker_glueDataObjι_appTop U

end AlgebraicGeometry.Scheme.IdealSheafData
