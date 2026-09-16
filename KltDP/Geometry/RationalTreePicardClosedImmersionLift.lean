import KltDP.Geometry.RationalTreePicardLeafInduction
import KltDP.Geometry.SchematicImageDenseOpen

/-!
# Lifting through the glued closed subscheme, and the component identification

For an ideal sheaf `I` on `X` and a quasi-compact morphism `g : W ⟶ X` with `I ≤ g.ker`, the
morphism `g` factors through `I.gluedTo : I.glueData.glued ⟶ X` (`liftGluedTo`,
`liftGluedTo_gluedTo`), uniquely since `I.gluedTo` is a monomorphism. The factorization is
built affine-locally: over an affine open `U` of `X`, the restriction `g ∣_ U` followed by
`U ≅ Spec Γ(X, U)` is a morphism into an affine scheme, hence `toSpecΓ` followed by `Spec` of
its transpose (`eq_toSpecΓ_comp_Spec_map`); the transpose kills `I(U)`, so it factors through
`Γ(X, U) ⧸ I(U)` by `Ideal.Quotient.lift` (`specQuotientLift`), and the chart
`Spec (Γ(X, U) ⧸ I(U))` maps into the glued scheme. The local lifts agree on overlaps because
`I.gluedTo` is a monomorphism, and are glued along the open cover of `W` by the preimages of the
affine opens (`Scheme.OpenCover.glueMorphisms`).

Instantiated to the components of a closed union of components (`componentUnionIdeal_le_ker`,
from the radical kernel of a reduced closed immersion), this gives the factorization
`componentFactorization` and therefore the identification data
`componentUnionIdentification X S : ComponentUnionIdentification X S` for every `X`, `S`;
`rationalTreePicard_trivial_of_exponents_zero'` is the assembled kernel statement with the
identification hypothesis discharged (only `InheritsLeafHypotheses` remains).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.RationalTreePicard

section SpecLift

variable {T : Scheme.{u}} {R : CommRingCat.{u}}

/-- A morphism into an affine scheme is the canonical map to `Spec Γ(T, ⊤)` followed by `Spec`
of its transpose. -/
theorem eq_toSpecΓ_comp_Spec_map (φ : T ⟶ Spec R) :
    φ = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ φ.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The lift of a morphism into `Spec R` through `Spec (R ⧸ J)`, when its transpose kills `J`. -/
def specQuotientLift (φ : T ⟶ Spec R) (J : Ideal R)
    (hJ : J ≤ RingHom.ker ((Scheme.ΓSpecIso R).inv ≫ φ.appTop).hom) :
    T ⟶ Spec (CommRingCat.of (R ⧸ J)) :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift J ((Scheme.ΓSpecIso R).inv ≫ φ.appTop).hom fun _ ha => hJ ha))

theorem specQuotientLift_comp (φ : T ⟶ Spec R) (J : Ideal R)
    (hJ : J ≤ RingHom.ker ((Scheme.ΓSpecIso R).inv ≫ φ.appTop).hom) :
    specQuotientLift φ J hJ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = φ := by
  rw [specQuotientLift, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.lift_comp_mk, CommRingCat.ofHom_hom]
  exact (eq_toSpecΓ_comp_Spec_map φ).symm

end SpecLift

section Lift

variable {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X) [QuasiCompact g]

/-- On an affine open, the transpose of the restricted morphism kills the ideal of `I`. -/
theorem ideal_le_ker_restrict (hI : I ≤ g.ker) (U : X.affineOpens) :
    I.ideal U ≤ RingHom.ker ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫
      ((g ∣_ U.1) ≫ U.2.isoSpec.hom).appTop).hom := by
  have hrestr : (g ∣_ U.1).appTop =
      (U.1.topIso.hom ≫ g.app U.1) ≫ (g ⁻¹ᵁ U.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using Γ_map_morphismRestrict g U.1
  have hcomp : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((g ∣_ U.1) ≫ U.2.isoSpec.hom).appTop =
      g.app U.1 ≫ (g ⁻¹ᵁ U.1).topIso.inv := by
    rw [Scheme.comp_appTop, U.2.isoSpec_hom_appTop, hrestr]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hinj : Function.Injective (g ⁻¹ᵁ U.1).topIso.inv.hom :=
    (g ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv.injective
  rw [hcomp, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj, ← Scheme.Hom.ker_apply]
  exact hI U

/-- The local factorization over an affine open, into the glued scheme. -/
def localLift (hI : I ≤ g.ker) (U : X.affineOpens) :
    (g ⁻¹ᵁ U.1).toScheme ⟶ I.glueData.glued :=
  specQuotientLift ((g ∣_ U.1) ≫ U.2.isoSpec.hom) (I.ideal U) (ideal_le_ker_restrict I g hI U) ≫
    I.glueData.ι U

theorem localLift_gluedTo (hI : I ≤ g.ker) (U : X.affineOpens) :
    localLift I g hI U ≫ I.gluedTo = (g ⁻¹ᵁ U.1).ι ≫ g := by
  rw [localLift, Category.assoc, Scheme.IdealSheafData.ι_gluedTo,
    Scheme.IdealSheafData.glueDataObjι_ι, ← Category.assoc, specQuotientLift_comp,
    Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, morphismRestrict_ι]

omit [QuasiCompact g] in
theorem iSup_preimage_affineOpens_eq_top :
    ⨆ U : X.affineOpens, g ⁻¹ᵁ (U : X.Opens) = ⊤ :=
  g.preimage_iSup_eq_top (iSup_affineOpens_eq_top X)

/-- The open cover of the source by the preimages of the affine opens of the target. -/
def preimageAffineCover : W.OpenCover :=
  W.openCoverOfISupEqTop (fun U : X.affineOpens => g ⁻¹ᵁ (U : X.Opens))
    (iSup_preimage_affineOpens_eq_top g)

/-- The factorization of `g` through the glued closed subscheme of `I ≤ g.ker`. -/
def liftGluedTo (hI : I ≤ g.ker) : W ⟶ I.glueData.glued :=
  (preimageAffineCover g).glueMorphisms (fun U => localLift I g hI U) fun U V => by
    rw [← cancel_mono I.gluedTo, Category.assoc, Category.assoc, localLift_gluedTo,
      localLift_gluedTo, ← Category.assoc, ← Category.assoc]
    congr 1
    exact pullback.condition

theorem liftGluedTo_gluedTo (hI : I ≤ g.ker) : liftGluedTo I g hI ≫ I.gluedTo = g :=
  (preimageAffineCover g).hom_ext _ _ fun U => by
    rw [← Category.assoc, liftGluedTo, Scheme.Cover.ι_glueMorphisms, localLift_gluedTo]
    rfl

/-- The factorization is unique: `I.gluedTo` is a monomorphism. -/
theorem eq_liftGluedTo (hI : I ≤ g.ker) (g' : W ⟶ I.glueData.glued)
    (hg' : g' ≫ I.gluedTo = g) : g' = liftGluedTo I g hI := by
  rw [← cancel_mono I.gluedTo, hg', liftGluedTo_gluedTo]

end Lift

section Components

variable (X : Scheme.{u}) [NoetherianSpace X] (S : Set ↥(irreducibleComponents X))

/-- The vanishing ideal of an original component is contained in the kernel of the closed
immersion of the corresponding component of the closed union (whose kernel is radical, with
support that component). -/
theorem componentUnionIdeal_le_ker (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentUnionIdeal X {componentImage X S D'} ≤
      (componentUnionInclusion (componentUnionScheme X S) {D'} ≫
        componentUnionInclusion X S).ker := by
  have hrad : (componentUnionInclusion (componentUnionScheme X S) {D'} ≫
      componentUnionInclusion X S).ker =
      Scheme.IdealSheafData.vanishingIdeal (componentUnionInclusion (componentUnionScheme X S) {D'} ≫
        componentUnionInclusion X S).ker.support := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, SchematicImageDenseOpen.ker_radical]
  rw [hrad, componentUnionIdeal]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  show ((componentUnionInclusion (componentUnionScheme X S) {D'} ≫
      componentUnionInclusion X S).ker.support : Set X) ⊆
    (componentClosedUnion X {componentImage X S D'} : Set X)
  rw [Scheme.Hom.support_ker, coe_componentClosedUnion_singleton]
  have hrange : Set.range (componentUnionInclusion (componentUnionScheme X S) {D'} ≫
      componentUnionInclusion X S).base = (componentImage X S D').1 := by
    rw [Scheme.comp_base, TopCat.coe_comp, Set.range_comp, range_componentUnionInclusion,
      coe_componentClosedUnion_singleton, image_componentImage]
  rw [hrange]
  exact (isClosed_of_mem_irreducibleComponents _ (componentImage X S D').2).closure_subset

/-- The factorization of the component inclusion of the closed union through the reduced closed
subscheme of the corresponding original component. -/
def componentFactorization (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentUnionScheme (componentUnionScheme X S) {D'} ⟶
      componentUnionScheme X {componentImage X S D'} :=
  liftGluedTo (componentUnionIdeal X {componentImage X S D'}) _ (componentUnionIdeal_le_ker X S D')

theorem componentFactorization_comp (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentFactorization X S D' ≫ componentUnionInclusion X {componentImage X S D'} =
      componentUnionInclusion (componentUnionScheme X S) {D'} ≫ componentUnionInclusion X S :=
  liftGluedTo_gluedTo _ _ _

/-- The identification data of the components of every closed union of components. -/
def componentUnionIdentification : ComponentUnionIdentification X S :=
  componentUnionIdentificationOfFactorization X S (componentFactorization X S)
    (componentFactorization_comp X S)

end Components

section Kernel

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The kernel statement of `lem:tree-picard`, with the identification data discharged: only the
inheritance of the component-point tree and of the transverse germs remains as a hypothesis. -/
theorem rationalTreePicard_trivial_of_exponents_zero' (hinherit : InheritsLeafHypotheses.{u})
    (n : ℕ) :
    ∀ (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
      [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      Nat.card ↥(irreducibleComponents X) = n →
      topologicalKrullDim X ≤ 1 → (componentPointIncidenceGraph X).IsTree →
      HasTransverseComponentBranches X → ExponentsZeroTrivial k X :=
  rationalTreePicard_trivial_of_exponents_zero k (fun Y _ S => componentUnionIdentification Y S)
    hinherit n

/-- The kernel half of `lem:tree-picard` with the identification data discharged. -/
theorem multidegreeHom_injective_of_inheritance' (hinherit : InheritsLeafHypotheses.{u})
    (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Injective (multidegreeHom k X e) :=
  multidegreeHom_injective_of_inheritance k (fun Y _ S => componentUnionIdentification Y S)
    hinherit X f hdim hTree htrans e

end Kernel

end KltDP.Geometry.RationalTreePicard
