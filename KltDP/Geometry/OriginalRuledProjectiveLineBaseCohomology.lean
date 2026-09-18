import KltDP.Geometry.RuledProjectiveLineBaseCohomology
import KltDP.Geometry.RegularResolutionStructureCohomology
import KltDP.Geometry.SurfacePointBlowupSequenceBirational

/-! Structure cohomology on the original source of the actual ruled-model blowdown. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RuledProjectiveLineBase

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S V : NormalProjectiveSurface k}

/-- Transport the computed invariants through the same original blowdown.
No cohomology value or rationality of either surface is an input. -/
theorem source_structureCohomology
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
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
    (eC : C ≅ projectiveSpace k 1) (heC : eC.hom ≫ projectiveSpaceToSpec k 1 = c) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 = 0 ∧
      eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) = 1 := by
  have hVcoh := structureCohomology V hV C c hCdim hCreg q hbase hsurj hfib σ hσ eC heC
  have hres : IsResolution S V b :=
    ⟨hb.over_base, hS, (isBirational_iff_isBirationalScheme b).mpr hb.isBirationalScheme⟩
  exact ⟨(hres.structureSheaf_cohomologyDimension_eq_of_regular_target hV 1).trans hVcoh.1,
    (hres.structureSheaf_eulerCharacteristic_eq_of_regular_target hV).trans hVcoh.2⟩

end KltDP.Geometry.RuledProjectiveLineBase

#print axioms KltDP.Geometry.RuledProjectiveLineBase.source_structureCohomology
