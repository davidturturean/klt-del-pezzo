import KltDP.Geometry.RuledProjectiveLineBaseUnimodular
import KltDP.Geometry.OriginalRuledProjectiveLineBaseCohomology
import KltDP.Geometry.RegularResolutionPicardUnimodular
import KltDP.Geometry.PicardUnimodularTorsionFree

/-!
# Original source invariants through the same ruling over the projective line

The original ruled model supplies its actual integral Picard unimodularity
and structure cohomology. The given original blowdown transports both to
the original source; torsion-freeness follows from the integral dual map.
Neither surface is assumed to have a birational rationality witness.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RuledProjectiveLineBase

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S V : NormalProjectiveSurface k}

/-- Both actual surfaces retain their native invariants through the same b. -/
theorem source_invariants
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
    V.PicardUnimodular hV ∧ S.PicardUnimodular hS ∧ S.PicardTorsionFree ∧
      cohomologyDimension V.structureMorphism
        (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1 = 0 ∧
      eulerCharacteristic V.structureMorphism
        (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) = 1 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 = 0 ∧
      eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) = 1 := by
  have hVU := picardUnimodular V hV C c hCdim hCreg q hbase hsurj hfib σ hσ eC
  have hres : IsResolution S V b :=
    ⟨hb.over_base, hS, (isBirational_iff_isBirationalScheme b).mpr hb.isBirationalScheme⟩
  have hSU : S.PicardUnimodular hS := (hres.picardUnimodular_iff hV).mpr hVU
  have hVcoh := structureCohomology V hV C c hCdim hCreg q hbase hsurj hfib σ hσ eC heC
  have hScoh := source_structureCohomology b hb hS hV C c hCdim hCreg
    q hbase hsurj hfib σ hσ eC heC
  exact ⟨hVU, hSU, S.picardTorsionFree_of_picardUnimodular hS hSU,
    hVcoh.1, hVcoh.2, hScoh.1, hScoh.2⟩

end KltDP.Geometry.RuledProjectiveLineBase

#print axioms KltDP.Geometry.RuledProjectiveLineBase.source_invariants
