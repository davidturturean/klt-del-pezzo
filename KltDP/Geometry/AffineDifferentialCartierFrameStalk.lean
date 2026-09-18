import KltDP.Geometry.CartierFrameLocalGeneration
import KltDP.Geometry.AffineDifferentialExteriorStalkModule

/-!
# The actual Cartier frame is primitive in the original affine stalk

Every stalk element has an original section representative. On its
intersection with the original Cartier chart, the accepted equation
trivialization expresses that representative in the original frame.
The proved original germ multiplication then gives stalk generation and
unit coordinates under every actual stalk-linear trivialization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialCartierFrameStalk

open AffineDifferentialExteriorOriginalStalk
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing)
open CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))
    (D : CartierDivisor (Spec (CommRingCat.of A)))
    (e : cartierDivisorModule (Spec (CommRingCat.of A)) D ≅
      SchemeExteriorPower.sheaf
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n)
    (c : CartierEquationChart (Spec (CommRingCat.of A)) D) (hpc : p ∈ c.openSet)

/-- Every actual intrinsic stalk element is a scalar multiple of the
germ of the given original Cartier frame. -/
theorem exists_smul_frame (z : (presheaf k A n).stalk p) :
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
    ∃ a : originalStalkRing A p,
      a • (presheaf k A n).germ c.openSet p hpc
        (frame (Spec (CommRingCat.of A)) D _ e c) = z := by
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
  let M := SchemeExteriorPower.sheaf
    (SchemeKaehlerSheaf.baseRingSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n
  obtain ⟨U, hpU, s, hs⟩ := (presheaf k A n).germ_exist p z
  let V : (Spec (CommRingCat.of A)).Opens := U ⊓ c.openSet
  have hpV : p ∈ V := ⟨hpU, hpc⟩
  letI : Nonempty V.toScheme := ⟨⟨p, hpV⟩⟩
  letI vm := intrinsicSectionModule k A n V
  letI : SMul Γ(Spec (CommRingCat.of A), V) ((presheaf k A n).obj (op V)) := vm.toSMul
  let iU : V ⟶ U := homOfLE inf_le_left
  let ic : V ⟶ c.openSet := homOfLE inf_le_right
  obtain ⟨a, ha⟩ := CartierFrameLocalGeneration.exists_smul_frame_on
    (Spec (CommRingCat.of A)) D c V ic.le M e (M.val.map iU.op s)
  have ha' : a • (presheaf k A n).map ic.op
      (frame (Spec (CommRingCat.of A)) D M e c) =
    (presheaf k A n).map iU.op s := ha
  refine ⟨(Spec (CommRingCat.of A)).presheaf.germ V p hpV a, ?_⟩
  calc
    (Spec (CommRingCat.of A)).presheaf.germ V p hpV a •
        (presheaf k A n).germ c.openSet p hpc
          (frame (Spec (CommRingCat.of A)) D M e c) =
      (Spec (CommRingCat.of A)).presheaf.germ V p hpV a •
        (presheaf k A n).germ V p hpV ((presheaf k A n).map ic.op
          (frame (Spec (CommRingCat.of A)) D M e c)) :=
      congrArg ((Spec (CommRingCat.of A)).presheaf.germ V p hpV a • ·)
        ((presheaf k A n).germ_res_apply ic p hpV
          (frame (Spec (CommRingCat.of A)) D M e c)).symm
    _ = (presheaf k A n).germ V p hpV
        (a • (presheaf k A n).map ic.op (frame (Spec (CommRingCat.of A)) D M e c)) :=
      (stalkModuleOfBasis_germ_smul k A p b V hpV a
        ((presheaf k A n).map ic.op (frame (Spec (CommRingCat.of A)) D M e c))).symm
    _ = (presheaf k A n).germ V p hpV ((presheaf k A n).map iU.op s) :=
      congrArg ((presheaf k A n).germ V p hpV) ha'
    _ = z := ((presheaf k A n).germ_res_apply iU p hpV s).trans hs

/-- Every actual linear coordinate sends the original Cartier frame to
a unit; no unit or primitive-frame assumption is supplied. -/
theorem coordinate_frame_isUnit :
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
    ∀ t : ((presheaf k A n).stalk p) ≃ₗ[originalStalkRing A p] originalStalkRing A p,
      IsUnit (t ((presheaf k A n).germ c.openSet p hpc
        (frame (Spec (CommRingCat.of A)) D _ e c))) := by
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
  dsimp only
  intro t
  obtain ⟨a, ha⟩ := exists_smul_frame k A p b D e c hpc (t.symm 1)
  apply isUnit_of_mul_eq_one_right a
  simpa only [map_smul, smul_eq_mul, LinearEquiv.apply_symm_apply] using congrArg t ha

/-- The actual original section coefficient is its stalk coordinate,
up to the proved unit coordinate of the actual Cartier frame. -/
theorem coordinate_germ_eq_coefficient_mul_frame
    (s : (presheaf k A n).obj (op c.openSet)) :
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
    ∀ t : ((presheaf k A n).stalk p) ≃ₗ[originalStalkRing A p] originalStalkRing A p,
      t ((presheaf k A n).germ c.openSet p hpc s) =
        (Spec (CommRingCat.of A)).presheaf.germ c.openSet p hpc
          (sectionCoefficient (Spec (CommRingCat.of A)) D _ e c s) *
          t ((presheaf k A n).germ c.openSet p hpc
            (frame (Spec (CommRingCat.of A)) D _ e c)) := by
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul (originalStalkRing A p) ((presheaf k A n).stalk p) := sm.toSMul
  dsimp only
  intro t
  letI cm := intrinsicSectionModule k A n c.openSet
  letI : SMul Γ(Spec (CommRingCat.of A), c.openSet)
    ((presheaf k A n).obj (op c.openSet)) := cm.toSMul
  have h := congrArg (fun s => t ((presheaf k A n).germ c.openSet p hpc s))
    (sectionCoefficient_smul_frame (Spec (CommRingCat.of A)) D _ e c s)
  dsimp only at h
  have hg := stalkModuleOfBasis_germ_smul k A p b c.openSet hpc
    (sectionCoefficient (Spec (CommRingCat.of A)) D _ e c s)
    (frame (Spec (CommRingCat.of A)) D _ e c)
  have ht := congrArg t hg
  have ht' := t.map_smul
    ((Spec (CommRingCat.of A)).presheaf.germ c.openSet p hpc
      (sectionCoefficient (Spec (CommRingCat.of A)) D _ e c s))
    ((presheaf k A n).germ c.openSet p hpc (frame (Spec (CommRingCat.of A)) D _ e c))
  exact h.symm.trans (ht.trans (by simpa only [smul_eq_mul] using ht'))

end KltDP.Geometry.AffineDifferentialCartierFrameStalk

#check @KltDP.Geometry.AffineDifferentialCartierFrameStalk.coordinate_frame_isUnit
#check @KltDP.Geometry.AffineDifferentialCartierFrameStalk.coordinate_germ_eq_coefficient_mul_frame
#print axioms KltDP.Geometry.AffineDifferentialCartierFrameStalk.coordinate_frame_isUnit
