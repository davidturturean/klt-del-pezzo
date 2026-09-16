import KltDP.Geometry.AffineModuleTildeExteriorFrame

/-!
# Invertibility of the original affine top exterior comparison

Transport the native module basis through the original affine global-section
isomorphisms. The original tilde-to-exterior map sends its native basis wedge
to the corresponding intrinsic wedge, with coefficient one. The resulting
coordinate formula proves its global-section map bijective. The already
proved original exterior counit then proves the original sheaf map invertible.

The forward map is unchanged. Both inverse laws concern this exact map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTildeExteriorMap

open AffineModuleTilde AffineTopDifferentialFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original affine global-section ring isomorphism, in its forward order. -/
def topRingEquiv (R : Type u) [CommRing R] : R ≃+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

theorem topRingEquiv_apply (R : Type u) [CommRing R] (r : R) :
    topRingEquiv R r = StructureSheaf.toOpen R ⊤ r := rfl

variable {R : Type u} [CommRing R]

local instance topRingCatCommRing :
    CommRing ((Spec (.of R)).ringCatSheaf.val.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(Spec (.of R), ⊤))

local instance topSectionRingModule (N : (Spec (.of R)).Modules) :
    Module Γ(Spec (.of R), ⊤) (sectionModule N ⊤) :=
  (N.val.obj (op ⊤)).isModule

local instance topOriginalScalarModule (N : (Spec (.of R)).Modules) :
    Module R (N.val.obj (op ⊤)) := (sectionModule N ⊤).isModule

variable (M : ModuleCat.{u} R) {n : ℕ} (b : Basis (Fin n) R M)

/-- The actual global-section basis, with scalars changed only along ΓSpec. -/
def topSectionBasis :
    Basis (Fin n) Γ(Spec (.of R), ⊤) (M.tilde.val.obj (op ⊤)) := by
  let b₀ : Basis (Fin n) R (sectionModule M.tilde ⊤) :=
    b.map (isoTop M).toLinearEquiv
  exact b₀.mapCoeffs (topRingEquiv R) (fun r s =>
    (sectionModule_smul_toOpen M.tilde ⊤ r s).symm)

/-- Its vectors are the original canonical sections of the native basis. -/
theorem topSectionBasis_apply (i : Fin n) :
    topSectionBasis M b i = ModuleCat.Tilde.toOpen M ⊤ (b i) := by
  let b₀ : Basis (Fin n) R (sectionModule M.tilde ⊤) :=
    b.map (isoTop M).toLinearEquiv
  have h := b₀.mapCoeffs_apply (topRingEquiv R)
    (fun r s => (sectionModule_smul_toOpen M.tilde ⊤ r s).symm) i
  exact h.trans ((b.map_apply (isoTop M).toLinearEquiv i).trans rfl)

/-- The original exterior unit on the whole affine scheme. -/
def topUnitIso :
    (SchemeExteriorPower.presheaf M.tilde n).obj (op ⊤) ≅
      (SchemeExteriorPower.sheaf M.tilde n).val.obj (op ⊤) := by
  letI := unit_isIso M b ⊤
  exact asIso ((SchemeExteriorPower.toSheaf M.tilde n).app (op ⊤))

/-- Actual top exterior sections have determinant coordinates in this basis. -/
def topExteriorCoordinate :
    (SchemeExteriorPower.sheaf M.tilde n).val.obj (op ⊤) ≃ₗ[Γ(Spec (.of R), ⊤)]
      Γ(Spec (.of R), ⊤) :=
  (topUnitIso M b).symm.toLinearEquiv ≪≫ₗ
    determinantEquiv (topSectionBasis M b)

theorem topExteriorCoordinate_toSheaf
    (q : (SchemeExteriorPower.presheaf M.tilde n).obj (op ⊤)) :
    topExteriorCoordinate M b ((SchemeExteriorPower.toSheaf M.tilde n).app (op ⊤) q) =
      determinantEquiv (topSectionBasis M b) q :=
  congrArg (determinantEquiv (topSectionBasis M b))
    (show (topUnitIso M b).inv ((topUnitIso M b).hom q) = q from
      ConcreteCategory.congr_hom (topUnitIso M b).hom_inv_id q)

/-- The compiled map sends the original native basis wedge to coefficient one. -/
theorem topExteriorCoordinate_nativeBasis :
    topExteriorCoordinate M b
      (toSectionMap M n ⊤ (exteriorPower.ιMulti R n b)) = 1 := by
  rw [toSectionMap_wedge]
  change topExteriorCoordinate M b
    ((SchemeExteriorPower.toSheaf M.tilde n).app (op ⊤)
      (exteriorPower.ιMulti Γ(Spec (.of R), ⊤) n
        (fun i => ModuleCat.Tilde.toOpen M ⊤ (b i)))) = 1
  rw [topExteriorCoordinate_toSheaf, determinantEquiv_apply_wedge]
  exact (congrArg (topSectionBasis M b).det
    (funext (fun i => (topSectionBasis_apply M b i).symm))).trans
      (topSectionBasis M b).det_self

/-- The entire original global-section map has the original ΓSpec coefficient. -/
theorem topExteriorCoordinate_toSectionMap (ω : M.exteriorPower n) :
    topExteriorCoordinate M b (toSectionMap M n ⊤ ω) =
      topRingEquiv R (determinantEquiv b ω) := by
  let E := SchemeExteriorPower.sheaf M.tilde n
  let q : M.exteriorPower n := exteriorPower.ιMulti R n b
  have hω : determinantEquiv b ω • q = ω :=
    (determinantEquiv_symm_apply b (determinantEquiv b ω)).symm.trans
      ((determinantEquiv b).symm_apply_apply ω)
  calc
    _ = topExteriorCoordinate M b (toSectionMap M n ⊤ (determinantEquiv b ω • q)) :=
      congrArg (fun η : M.exteriorPower n =>
        topExteriorCoordinate M b (toSectionMap M n ⊤ η)) hω.symm
    _ = topExteriorCoordinate M b
        (determinantEquiv b ω • (toSectionMap M n ⊤ q : sectionModule E ⊤)) :=
      congrArg (fun s : sectionModule E ⊤ => topExteriorCoordinate M b s)
        ((toSectionMap M n ⊤).hom.map_smul (determinantEquiv b ω) q)
    _ = topExteriorCoordinate M b
        (@SMul.smul Γ(Spec (.of R), ⊤) (E.val.obj (op ⊤))
          (E.val.obj (op ⊤)).isModule.toSMul
            (topRingEquiv R (determinantEquiv b ω)) (toSectionMap M n ⊤ q)) :=
      congrArg (fun s : E.val.obj (op ⊤) => topExteriorCoordinate M b s)
        (sectionModule_smul_toOpen E ⊤ (determinantEquiv b ω) (toSectionMap M n ⊤ q))
    _ = topRingEquiv R (determinantEquiv b ω) •
        topExteriorCoordinate M b (toSectionMap M n ⊤ q) :=
      (topExteriorCoordinate M b).map_smul
        (topRingEquiv R (determinantEquiv b ω)) (toSectionMap M n ⊤ q)
    _ = topRingEquiv R (determinantEquiv b ω) := by
      rw [topExteriorCoordinate_nativeBasis]
      change topRingEquiv R (determinantEquiv b ω) *
        (1 : Γ(Spec (.of R), ⊤)) = _
      exact mul_one _

include b in
/-- The actual global-section map is bijective, with no compatibility premise. -/
theorem toSectionMap_top_bijective : Function.Bijective (toSectionMap M n ⊤) := by
  have he : (fun ω : M.exteriorPower n =>
      topExteriorCoordinate M b (toSectionMap M n ⊤ ω)) =
      (fun ω => topRingEquiv R (determinantEquiv b ω)) :=
    funext (topExteriorCoordinate_toSectionMap M b)
  have hb : Function.Bijective (fun ω : M.exteriorPower n =>
      topExteriorCoordinate M b (toSectionMap M n ⊤ ω)) := by
    rw [he]
    exact (topRingEquiv R).bijective.comp (determinantEquiv b).bijective
  constructor
  · intro x y hxy
    exact hb.1 (congrArg (topExteriorCoordinate M b) hxy)
  · intro s
    obtain ⟨ω, hω⟩ := hb.2 (topExteriorCoordinate M b s)
    exact ⟨ω, (topExteriorCoordinate M b).injective hω⟩

include b in
theorem toSectionMap_top_isIso : IsIso (toSectionMap M n ⊤) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (toSectionMap_top_bijective M b)

include b in
/-- The original native tilde-to-exterior map is an isomorphism. -/
theorem map_isIso : IsIso (map M n) := by
  letI := toSectionMap_top_isIso M b
  letI := counit_isIso M b
  let e := (AffineModuleTilde.functor R).mapIso (asIso (toSectionMap M n ⊤)) ≪≫
    asIso (AffineModuleTilde.counit (SchemeExteriorPower.sheaf M.tilde n))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Package the inverse of the proved original map, retaining its forward map. -/
def isoOfBasis : (M.exteriorPower n).tilde ≅ SchemeExteriorPower.sheaf M.tilde n := by
  letI := map_isIso M b
  exact asIso (map M n)

theorem isoOfBasis_hom : (isoOfBasis M b).hom = map M n := rfl

def inverseOfBasis : SchemeExteriorPower.sheaf M.tilde n ⟶ (M.exteriorPower n).tilde :=
  (isoOfBasis M b).inv

theorem map_inverseOfBasis : map M n ≫ inverseOfBasis M b = 𝟙 _ :=
  (isoOfBasis M b).hom_inv_id

theorem inverseOfBasis_map : inverseOfBasis M b ≫ map M n = 𝟙 _ :=
  (isoOfBasis M b).inv_hom_id

end KltDP.Geometry.AffineModuleTildeExteriorMap
