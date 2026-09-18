import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.SchemeKaehlerPullbackRestrictionComp
import KltDP.Geometry.ProjectiveLineCanonicalFormula

/-!
# Canonical degree under an original scheme isomorphism over the field

The differential pullback isomorphism and the existing scalar Euler transport
identify both terms in the original canonical degree. In particular every
original curve isomorphic over the field to the projective line has canonical
degree minus two. No duality or general genus formula is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CurveCanonical

open ModuleCohomology

variable {k : Type u} [Field k] {C D : Scheme.{u}}

/-- Canonical degree is invariant under an actual scheme isomorphism over the field. -/
theorem canonicalDegree_eq_of_schemeIso (e : C ≅ D)
    (f : C ⟶ Spec (CommRingCat.of k)) (g : D ⟶ Spec (CommRingCat.of k))
    (he : e.hom ≫ g = f) : canonicalDegree f = canonicalDegree g := by
  have hinv : e.inv ≫ f = g := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hOmega : eulerCharacteristic f (cotangentSheaf f) =
      eulerCharacteristic g (cotangentSheaf g) := by
    calc
      eulerCharacteristic f (cotangentSheaf f) =
          eulerCharacteristic g ((schemeModulePullback e.inv).obj (cotangentSheaf f)) :=
        eulerCharacteristic_eq_pullback_inv e f g he (cotangentSheaf f)
      _ = eulerCharacteristic g (cotangentSheaf (e.inv ≫ f)) :=
        eulerCharacteristic_eq_of_iso g (SchemeKaehlerOpenRestriction.pullbackIso f e.inv)
      _ = eulerCharacteristic g (cotangentSheaf g) := by rw [hinv]
  unfold canonicalDegree
  rw [hOmega, eulerCharacteristic_unit_eq e f g he]

/-- An original curve isomorphic over the field to the projective line has degree minus two. -/
theorem canonicalDegree_eq_neg_two_of_projectiveLineIso
    (f : C ⟶ Spec (CommRingCat.of k))
    (e : C ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = f) : canonicalDegree f = -2 :=
  (canonicalDegree_eq_of_schemeIso e f (projectiveSpaceToSpec k 1) he).trans
    (ProjectiveLineCanonicalFormula.canonicalDegree_eq_neg_two k)

end KltDP.Geometry.CurveCanonical
