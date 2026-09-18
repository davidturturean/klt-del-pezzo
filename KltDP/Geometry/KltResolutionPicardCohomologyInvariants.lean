import KltDP.Geometry.KltRuledBaseProjectiveLine
import KltDP.Geometry.KltResolutionRationalRuledModel
import KltDP.Geometry.OriginalRuledProjectiveLineBaseInvariants
import KltDP.Geometry.RationalSurfacePicardInvariants
import KltDP.Geometry.RationalSurfaceStructureCohomology

/-! The original minimal resolution of a rank-one positive-characteristic
klt del Pezzo surface has an actual unimodular and torsion-free Picard group,
h1(O)=0 and chi(O)=1. These native invariants are derived by constructing
the rational-or-ruled model and proving that its actual ruled base is P1.
No rationality or genus assertion is added as an input. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- Native Picard and cohomological invariants on the original source. -/
theorem picard_and_structure_invariants_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p) :
    S.PicardUnimodular hmin.regular ∧ S.PicardTorsionFree ∧
      eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) = 1 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 = 0 := by
  obtain ⟨V, hV, b, hb, _, _, _, hmodel⟩ :=
    hmin.toIsResolution.exists_rational_or_ruled_model_of_kltDelPezzo hDP
  rcases hmodel with hrational | hruled
  · have hU := S.picardUnimodular_of_birationalOver_affinePlane hmin.regular hrational
    have hcoh := S.structureCohomology_of_rational hmin.regular hrational
    exact ⟨hU, S.picardTorsionFree_of_picardUnimodular hmin.regular hU,
      hcoh.1, hcoh.2.1⟩
  · obtain ⟨C, c, hCi, hCft, hCqc, hCsep, hCp, _, hCdim, hCreg,
      q, hbase, _, hsurj, hfib, _, _, _, σ, hσ⟩ := hruled
    letI : IsIntegral C := hCi
    letI : LocallyOfFiniteType c := hCft
    letI : QuasiCompact c := hCqc
    letI : IsSeparated c := hCsep
    letI : IsProper c := hCp
    obtain ⟨eC, heC⟩ := KltRuledBaseProjectiveLine.exists_iso
      π hmin hDP hrank p hp b hb hV C c hCdim hCreg q hbase hsurj hfib σ hσ
    obtain ⟨_, hU, htf, _, _, h1, hχ⟩ := RuledProjectiveLineBase.source_invariants
      b hb hmin.regular hV C c hCdim hCreg q hbase hsurj hfib σ hσ eC heC
    exact ⟨hU, htf, hχ, h1⟩

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.picard_and_structure_invariants_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.picard_and_structure_invariants_of_kltDelPezzo
