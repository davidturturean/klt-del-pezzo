import KltDP.Geometry.AffineModuleTildePullback
import KltDP.Geometry.AffineModuleCounitIsomorphism
import KltDP.Geometry.AffineModuleChartDenominators

/-!
# The actual structure sheaf of an affine closed component

For the original affine map Spec B → Spec A, global sections of the
pushforward unit are the original A-module B. Its original basic-open
restrictions satisfy denominator extension because their inverse images
are D(a) ↦ D(algebraMap A B a). The existing affine counit theorem therefore
gives an actual module-sheaf isomorphism from the tilde of B to this
pushforward, retaining the original global sections and restrictions.

The quotient specialization identifies the original A/I tilde module
with the structure-sheaf pushforward along Spec(A/I) → Spec A. It assumes
neither quasicoherence of the pushforward nor a desired comparison map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.RationalTreePicard

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The original affine map of the two actual spectra. -/
abbrev componentAffineMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The original pushforward module sheaf. -/
abbrev componentPushforward (M : (Spec (CommRingCat.of B)).Modules) :
    (Spec (CommRingCat.of A)).Modules :=
  (schemeModulePushforward (componentAffineMap A B)).obj M

/-- The base-ring action on the original pushforward sections is the
original component action through the specified algebra map. -/
theorem componentPushforward_smul (M : (Spec (CommRingCat.of B)).Modules)
    (U : (Spec (CommRingCat.of A)).Opens) (a : A)
    (s : sectionModule (componentPushforward A B M) U) :
    (a • s : sectionModule (componentPushforward A B M) U) =
      algebraMap A B a •
        (show sectionModule M ((componentAffineMap A B) ⁻¹ᵁ U) from s) := by
  let smul : Γ(Spec (CommRingCat.of B), (componentAffineMap A B) ⁻¹ᵁ U) →
      M.val.obj (op ((componentAffineMap A B) ⁻¹ᵁ U)) →
      M.val.obj (op ((componentAffineMap A B) ⁻¹ᵁ U)) :=
    @SMul.smul _ _ (M.val.obj (op ((componentAffineMap A B) ⁻¹ᵁ U))).isModule.toSMul
  change smul ((componentAffineMap A B).app U (StructureSheaf.toOpen A U a)) s =
    smul (StructureSheaf.toOpen B ((componentAffineMap A B) ⁻¹ᵁ U) (algebraMap A B a)) s
  exact congrArg (fun r => smul r s)
    (ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap (algebraMap A B) U) a)

/-- Original denominator extension survives the actual affine pushforward.
The proof retains the same power and the same original extending section. -/
theorem componentPushforward_denominatorExtension_top
    (M : (Spec (CommRingCat.of B)).Modules) (h : DenominatorExtension M ⊤) :
    DenominatorExtension (componentPushforward A B M) ⊤ where
  existence a ha s := by
    obtain ⟨n, t, ht⟩ := h.existence (algebraMap A B a) le_top s
    refine ⟨n, t, ?_⟩
    rw [componentPushforward_smul A B M (PrimeSpectrum.basicOpen a) (a ^ n) s, map_pow]
    exact ht
  uniqueness a ha t ht := by
    have ht' : sectionRestrict M
        (le_top : PrimeSpectrum.basicOpen (algebraMap A B a) ≤ ⊤) t = 0 := ht
    obtain ⟨n, hn⟩ := h.uniqueness (algebraMap A B a) le_top t ht'
    refine ⟨n, ?_⟩
    rw [componentPushforward_smul A B M ⊤ (a ^ n) t, map_pow]
    exact hn

/-- The original actual structure-sheaf pushforward from Spec B. -/
abbrev componentUnitPushforward : (Spec (CommRingCat.of A)).Modules :=
  componentPushforward A B (_root_.SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)

/-- The original affine counit of the structure-sheaf pushforward is an
isomorphism, derived from ring localization on Spec B. -/
theorem componentUnitPushforward_counit_isIso :
    IsIso (counit (componentUnitPushforward A B)) :=
  counit_isIso_of_denominatorExtension (componentUnitPushforward A B)
    (componentPushforward_denominatorExtension_top A B _ (unit_denominatorExtension_top B))

/-- The actual ΓSpec identification preserves the original A-module
action on B and on the original pushforward's global sections. -/
def componentUnitGlobalEquiv : B ≃ₗ[A] sectionModule (componentUnitPushforward A B) ⊤ where
  toFun b := (Scheme.ΓSpecIso (CommRingCat.of B)).inv b
  invFun s := (Scheme.ΓSpecIso (CommRingCat.of B)).hom s
  left_inv b := (Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply b
  right_inv s := (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply s
  map_add' b c := map_add _ b c
  map_smul' a b := by
    rw [Algebra.smul_def a b]
    have hs := componentPushforward_smul A B
      (_root_.SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) ⊤ a
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a * b) =
      a • (show sectionModule (componentUnitPushforward A B) ⊤ from
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    rw [hs]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a * b) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a) *
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv b
    exact map_mul _ _ _

/-- The literal tilde of the original A-module B is the actual affine
pushforward of the original structure-sheaf unit on Spec B. -/
def componentUnitTildePushforwardIso :
    (ModuleCat.of A B).tilde ≅ componentUnitPushforward A B := by
  letI := componentUnitPushforward_counit_isIso A B
  exact AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of A B) (N := sectionModule (componentUnitPushforward A B) ⊤)
    (componentUnitGlobalEquiv A B) ≪≫ asIso (counit (componentUnitPushforward A B))

/-- The comparison sends a canonical module section to the original
restriction of the corresponding ΓSpec section. -/
theorem componentUnitTildePushforwardIso_toOpen
    (U : (Spec (CommRingCat.of A)).Opens) (b : B) :
    (componentUnitTildePushforwardIso A B).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of A B) U b) =
      (componentUnitPushforward A B).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  change (counit (componentUnitPushforward A B)).val.app (op U)
      ((AffineModuleTilde.map (componentUnitGlobalEquiv A B).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of A B) U b)) = _
  rw [AffineModuleTilde.map_app_toOpen, counit_toOpen]
  rfl

/-- The actual quotient module sheaf is the pushforward of the actual
closed component's structure sheaf along its original quotient map. -/
def quotientTildePushforwardUnitIso (I : Ideal A) :
    (ModuleCat.of A (A ⧸ I)).tilde ≅
      (schemeModulePushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        (_root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf) :=
  componentUnitTildePushforwardIso A (A ⧸ I)

end KltDP.Geometry.RationalTreePicard
