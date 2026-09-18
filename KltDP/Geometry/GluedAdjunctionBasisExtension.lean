import KltDP.Geometry.SchemeModuleOpenLocality

/-!
# Use the pinned basis extension for the original adjunction module maps

The pinned `TopCat.Sheaf.restrictHomEquivHom` supplies the extension of
an additive basis morphism. Its scalar-linearity is checked on the same
basis using the original sheaf separation theorem. This is the bounded
module adapter for descent; it does not supply compatibility of the
adjunction chart maps, which is proved by their actual refinement squares.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v
namespace KltDP.Geometry.GluedAdjunctionBasisExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens)
  (hB : Opens.IsBasis (Set.range B)) {M N : X.Modules}

include hB in
/-- Linearity of an additive sheaf map is detected on the original open basis. -/
private theorem smul_of_basis (φ : M.val.presheaf ⟶ N.val.presheaf)
    (hφ : ∀ (i : ι) (r : X.ringCatSheaf.val.obj (op (B i)))
      (m : M.val.obj (op (B i))), φ.app (op (B i)) (r • m) = r • φ.app (op (B i)) m)
    (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.val.obj U) (m : M.val.obj U) :
    φ.app U (r • m) = r • φ.app U m := by
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨V, ⟨i, rfl⟩, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  refine ⟨B i, hVU, hxV, ?_⟩
  let p : U ⟶ op (B i) := (homOfLE hVU).op
  have hn (q : M.val.obj U) :
      N.val.map p (φ.app U q) = φ.app (op (B i)) (M.val.map p q) :=
    (ConcreteCategory.congr_hom (φ.naturality p) q).symm
  change N.val.map p (φ.app U (r • m)) = N.val.map p (r • φ.app U m)
  rw [hn, N.val.map_smul, M.val.map_smul, hφ, hn]

variable (φ : (inducedFunctor B).op ⋙ M.val.presheaf ⟶
    (inducedFunctor B).op ⋙ N.val.presheaf)
  (hφ : ∀ (i : ι) (r : X.ringCatSheaf.val.obj (op (B i)))
    (m : M.val.obj (op (B i))), φ.app (op i) (r • m) =
      r • (show N.val.obj (op (B i)) from φ.app (op i) m))

/-- The existing pinned extension, on the original additive sheaves. -/
private def additiveExtension : M.val.presheaf ⟶ N.val.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.val.presheaf
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N) hB φ

include hφ in
private theorem additiveExtension_smul (U : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.val.obj U) (m : M.val.obj U) :
    (additiveExtension B hB φ).app U (r • m) =
      r • (additiveExtension B hB φ).app U m := by
  apply smul_of_basis B hB (additiveExtension B hB φ)
  intro i a s
  simpa only [additiveExtension, TopCat.Sheaf.extend_hom_app] using hφ i a s

/-- The pinned basis extension is a morphism of the original module sheaves. -/
def hom : M ⟶ N :=
  ⟨PresheafOfModules.homMk (additiveExtension B hB φ)
    (additiveExtension_smul B hB φ hφ)⟩

/-- The extended original module map retains every original basis component. -/
theorem hom_app (i : ι) (m : M.val.obj (op (B i))) :
    (hom B hB φ hφ).val.app (op (B i)) m = φ.app (op i) m := by
  change (additiveExtension B hB φ).app (op (B i)) m = φ.app (op i) m
  rw [additiveExtension, TopCat.Sheaf.extend_hom_app]
  rfl

/-- The existing basis criterion detects invertibility of the extended original map. -/
theorem hom_isIso (hBij : ∀ i, Function.Bijective (φ.app (op i))) :
    IsIso (hom B hB φ hφ) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis (B := B) _ hB
  intro i
  change Function.Bijective (fun m => (hom B hB φ hφ).val.app (op (B i)) m)
  have hApp : (fun m => (hom B hB φ hφ).val.app (op (B i)) m) =
      (fun m => φ.app (op i) m) := by
    funext m
    exact hom_app B hB φ hφ i m
  rw [hApp]
  exact hBij i

end KltDP.Geometry.GluedAdjunctionBasisExtension
