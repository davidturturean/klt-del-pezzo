import KltDP.Geometry.CurveCanonicalRational
import KltDP.Literature.Hartshorne.RuledSurfaceGenus

/-!
# Original structure cohomology of a ruling over an actual projective line

The supplied isomorphism is over the original field and identifies the
unchanged base curve with the projective line. Its proved genus vanishing
and the complete ruled-surface genus theorem compute the original surface
H1 and Euler characteristic. No surface-rationality witness is required.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RuledProjectiveLineBase

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  (V : NormalProjectiveSurface k)
  (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1) (hCreg : ∀ y : C, RegularPoint C y)
  (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
  (hsurj : Function.Surjective q.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : q.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
  (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C)
  (eC : C ≅ projectiveSpace k 1) (heC : eC.hom ≫ projectiveSpaceToSpec k 1 = c)

include hV hCdim hCreg hbase hsurj hfib hσ heC

/-- The actual ruled surface has h1(O)=0 and chi(O)=1 over its original field. -/
theorem structureCohomology :
    cohomologyDimension V.structureMorphism
        (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 = 0 ∧
      eulerCharacteristic V.structureMorphism
        (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) = 1 := by
  have hgenus : CurveCanonical.genus c = 0 :=
    CurveCanonical.genus_eq_zero_of_projectiveLineIso c eC heC
  have h := Literature.Hartshorne.ruled_surface_genus_literal
    k V hV C c hCdim hCreg q hbase hsurj hfib σ hσ
  refine ⟨h.2.2.trans hgenus, ?_⟩
  have hEuler := h.1
  rw [hgenus, Nat.cast_zero, neg_zero] at hEuler
  omega

end KltDP.Geometry.RuledProjectiveLineBase

#print axioms KltDP.Geometry.RuledProjectiveLineBase.structureCohomology
