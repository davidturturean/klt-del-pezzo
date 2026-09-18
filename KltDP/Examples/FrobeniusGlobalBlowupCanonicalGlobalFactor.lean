import KltDP.Examples.FrobeniusGlobalBlowupCanonicalAffineFactor
import KltDP.Examples.FrobeniusGlobalBlowupCanonicalComplementFactor
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The original canonical factor on the whole next blowup stage

The actual affine Rees factor and unchanged-complement factor cover the
entire original next scheme. Transport the affine factor through the
original open-range isomorphism, then apply the accepted monic-factor
construction. Its composite is exactly the original projection differential.
The only extra hypothesis is smooth relative dimension two of the actual
old structure, already proved for every original projective contact stage.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalGlobalFactor

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine
open FrobeniusGlobalBlowupDifferentialComplement FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusGlobalBlowupCanonicalAffineFactor FrobeniusGlobalBlowupCanonicalComplementFactor

private def transportFactor {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N : C} (e : F.obj M ≅ F.obj N) : G.obj M ≅ G.obj N :=
  (c.app M).symm ≪≫ P.mapIso e ≪≫ c.app N

private theorem transportFactor_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N Q : C} (e : F.obj M ≅ F.obj N) (b : N ⟶ Q) (a : M ⟶ Q)
    (he : e.hom ≫ F.map b = F.map a) :
    (transportFactor F P G c e).hom ≫ G.map b = G.map a := by
  simp only [transportFactor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← c.hom.naturality b]
  change c.inv.app M ≫ P.map e.hom ≫ P.map (F.map b) ≫ c.hom.app Q = _
  rw [← Functor.map_comp_assoc, he]
  change c.inv.app M ≫ (F ⋙ P).map a ≫ c.hom.app Q = _
  rw [c.hom.naturality a, Iso.inv_hom_id_app_assoc]

variable {k : Type u} [Field k]

local instance wholeGlobalFactorOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k)

/-- The actual open image of the entire affine Rees blowup in the next scheme. -/
abbrev affineOpen : A.nextScheme.Opens := A.nextAffineBlowup.opensRange

def affineOpenIso : AffineBlowup.scheme (centerIdeal (k := k)) ≅ (affineOpen A).toScheme :=
  IsOpenImmersion.isoOfRangeEq A.nextAffineBlowup (affineOpen A).ι Subtype.range_coe.symm

theorem affineOpenIso_inv_fac :
    (affineOpenIso A).inv ≫ A.nextAffineBlowup = (affineOpen A).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac A.nextAffineBlowup (affineOpen A).ι Subtype.range_coe.symm

def affineOpenPullbackIso :
    schemeModulePullback A.nextAffineBlowup ⋙ schemeModulePullback (affineOpenIso A).inv ≅
      schemeModulePullback (affineOpen A).ι :=
  schemeModulePullbackCompIso (affineOpenIso A).inv A.nextAffineBlowup ≪≫
    eqToIso (congrArg schemeModulePullback (affineOpenIso_inv_fac A))

/-- The original affine factor transported to its actual covering open. -/
def affineOpenFactorIso :
    (schemeModulePullback (affineOpen A).ι).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback (affineOpen A).ι).obj (wholeCanonicalTarget A) :=
  transportFactor (schemeModulePullback A.nextAffineBlowup)
    (schemeModulePullback (affineOpenIso A).inv) (schemeModulePullback (affineOpen A).ι)
    (affineOpenPullbackIso A) (affineCanonicalFactorIso A)

theorem affineOpenFactorIso_comp :
    (affineOpenFactorIso A).hom ≫
        (schemeModulePullback (affineOpen A).ι).map (wholeCanonicalInclusion A) =
      (schemeModulePullback (affineOpen A).ι).map (nextDifferentialMap A) :=
  transportFactor_comp (schemeModulePullback A.nextAffineBlowup)
    (schemeModulePullback (affineOpenIso A).inv) (schemeModulePullback (affineOpen A).ι)
    (affineOpenPullbackIso A) (affineCanonicalFactorIso A)
    (wholeCanonicalInclusion A) (nextDifferentialMap A) (affineCanonicalFactorIso_comp A)

/-- The two original geometric opens cover the entire next scheme. -/
def wholeCoverOpen : Bool → A.nextScheme.Opens
  | false => affineOpen A
  | true => complementOpen A

theorem mem_wholeCoverOpen (x : A.nextScheme) : ∃ i, x ∈ wholeCoverOpen A i := by
  rcases PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed x with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨false, a, ha⟩
  · refine ⟨true, ?_⟩
    rw [← hb]
    change (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed ≫
        PointBlowupGluing.projection A.chart (originPoint (k := k)) A.center_closed).base b ∈
      PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed
    rw [PointBlowupGluing.complementι_projection]
    exact b.property

def wholeOpenFactorIso (i : Bool) :
    (schemeModulePullback (wholeCoverOpen A i).ι).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback (wholeCoverOpen A i).ι).obj (wholeCanonicalTarget A) :=
  match i with
  | false => affineOpenFactorIso A
  | true => complementCanonicalFactorIso A

theorem wholeOpenFactorIso_comp (i : Bool) :
    (wholeOpenFactorIso A i).hom ≫
        (schemeModulePullback (wholeCoverOpen A i).ι).map (wholeCanonicalInclusion A) =
      (schemeModulePullback (wholeCoverOpen A i).ι).map (nextDifferentialMap A) := by
  cases i with
  | false => exact affineOpenFactorIso_comp A
  | true => exact complementCanonicalFactorIso_comp A

variable [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- The original whole-stage canonical factor, constructed from the normalized original maps. -/
def wholeCanonicalBlowupIso :
    (schemeModulePullback A.nextProjection).obj (oldTop A) ≅ wholeCanonicalTarget A := by
  letI := wholeCanonicalInclusion_mono A
  exact schemeModuleMonicFactorIsoOnOpenCover (wholeCoverOpen A) (mem_wholeCoverOpen A)
    (wholeCanonicalInclusion A) (nextDifferentialMap A) (wholeOpenFactorIso A)
    (wholeOpenFactorIso_comp A)

/-- Its composite is the original differential of the actual whole-stage projection. -/
theorem wholeCanonicalBlowupIso_comp :
    (wholeCanonicalBlowupIso A).hom ≫ wholeCanonicalInclusion A = nextDifferentialMap A := by
  letI := wholeCanonicalInclusion_mono A
  exact schemeModuleMonicFactorIsoOnOpenCover_comp (wholeCoverOpen A) (mem_wholeCoverOpen A)
    (wholeCanonicalInclusion A) (nextDifferentialMap A) (wholeOpenFactorIso A)
    (wholeOpenFactorIso_comp A)

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalGlobalFactor
