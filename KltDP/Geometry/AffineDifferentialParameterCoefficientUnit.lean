import KltDP.Geometry.AffineDifferentialCartierFrameStalk
import KltDP.Geometry.AffineDifferentialExteriorStalkLinearIso

/-!
# A genuine derivative basis gives a unit original Cartier coefficient

The original intrinsic parameter wedge maps to the given native basis
wedge through the proved original stalk-linear comparison. Its determinant
is one. The actual Cartier section-coordinate equality therefore proves
that the coefficient of this same parameter wedge is a local unit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialParameterCoefficientUnit

open SchemeKaehlerSheaf AffineDifferentialExteriorOriginalStalk
open AffineDifferentialCartierFrameStalk CartierRationalCoordinate
open AffineDifferentialExteriorStalkEvaluation
  (originalStalkRing stalkAffineAlgebra stalkGroundAlgebra stalkExteriorModule)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) (b : Basis (Fin 2) A (KaehlerDifferential k A))
    (D : CartierDivisor (Spec (CommRingCat.of A)))
    (e : cartierDivisorModule (Spec (CommRingCat.of A)) D ≅
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2)
    (c : CartierEquationChart (Spec (CommRingCat.of A)) D) (hpc : p ∈ c.openSet)
    (v : Fin 2 → A)

include b in
/-- The only parameter input is the actual native derivative basis.
Unitness of the literal original Cartier coefficient is derived. -/
theorem sectionCoefficient_wedge_isUnit :
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    ∀ bₚ : Basis (Fin 2) (originalStalkRing A p)
        (KaehlerDifferential k (originalStalkRing A p)),
      (∀ i, bₚ i = KaehlerDifferential.D k (originalStalkRing A p)
        (StructureSheaf.toStalk A p (v i))) →
      IsUnit ((Spec (CommRingCat.of A)).presheaf.germ c.openSet p hpc
        (sectionCoefficient (Spec (CommRingCat.of A)) D _ e c
          (SchemeExteriorPower.wedge
            (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 c.openSet
            (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
              (StructureSheaf.toOpen A c.openSet (v i)))))) := by
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  dsimp only
  intro bₚ hbₚ
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkExteriorModule k A p 2
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul (originalStalkRing A p) ((presheaf k A 2).stalk p) := sm.toSMul
  let t := (comparisonLinearIsoOfBasis k A p b).trans
    (AffineTopDifferentialFrame.determinantEquiv bₚ)
  let s := SchemeExteriorPower.wedge
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 c.openSet
    (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
      (StructureSheaf.toOpen A c.openSet (v i)))
  have htop : t ((presheaf k A 2).germ c.openSet p hpc s) = 1 := by
    change AffineTopDifferentialFrame.determinantEquiv bₚ
      (comparisonLinearIsoOfBasis k A p b ((presheaf k A 2).germ c.openSet p hpc s)) = 1
    rw [comparisonLinearIsoOfBasis_germ_wedge_D]
    have hv : (fun i => KaehlerDifferential.D k (originalStalkRing A p)
        (StructureSheaf.toStalk A p (v i))) = bₚ := funext (fun i => (hbₚ i).symm)
    rw [hv]
    exact AffineTopDifferentialFrame.determinantEquiv_basis_wedge bₚ
  have hco := coordinate_germ_eq_coefficient_mul_frame k A p b D e c hpc s t
  exact isUnit_of_mul_eq_one _
    (t ((presheaf k A 2).germ c.openSet p hpc
      (frame (Spec (CommRingCat.of A)) D _ e c))) (hco.symm.trans htop)

end KltDP.Geometry.AffineDifferentialParameterCoefficientUnit

#check @KltDP.Geometry.AffineDifferentialParameterCoefficientUnit.sectionCoefficient_wedge_isUnit
#print axioms KltDP.Geometry.AffineDifferentialParameterCoefficientUnit.sectionCoefficient_wedge_isUnit
