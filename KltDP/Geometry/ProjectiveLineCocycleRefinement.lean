import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.ProjectiveLinePicardExponent
import KltDP.Geometry.TransitionUnitPicardComparison
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The exponent of a pulled-back glued line bundle on `P¹` (BRIEF17, item 1)

The transition exponent of a line bundle on `P¹` (`ProjectiveLineSheafExponent.exponent`, read on the
standard two-chart cover) is computed from any cocycle presentation of its Picard class:

* `exponent_invertibleSheaf`, `value_picardClass`: the glued bundle of a standard-cover cocycle `g`
  has exponent `cocycleExponent k g`;
* `exponent_eq_of_refinement`: if `L.toPic` is the class of a cocycle `g` on *any* cover `U` that the
  standard opens refine (`σ`, `hσ : standardOpens i ≤ U (σ i)`), then `exponent k L` is the cocycle
  exponent of the refined cocycle `refinedUnits … σ hσ` (accepted `picardClass_eq_of_refinement`);
* `toPic_eq_picardClass_atlas`: the class of an invertible sheaf is the class of the transition
  cocycle of any of its atlases (the accepted argument of lane A1's `toPic_eq_picardClass'`);
* `exponent_pullback_eq`: for a section `s : P¹ ⟶ X` and `K` with `K.toPic = picardClass X U g`,
  `exponent k (s^* K) = cocycleExponent k (refinedUnits (s ⁻¹ᵁ U) (pullbackUnits s U g) σ hσ)`,
  given the pullback compatibility `PullbackGluedClass` (lane A1's accepted `pullbackGluedClass`
  proves it; its module could not be imported here because the dev711-07 tree carries a stale
  `RationalTreePicardLeafNodeCover`, so the property is a hypothesis `hP`), i.e. the Laurent exponent
  of the pulled-back transition unit between the two charts that receive the standard opens
  (`exponent_pullback_eq_overlapExponent`, `exponent_pullback_eq_of_monomial`).

The pulled-back cocycle (`pullbackUnits`) and its cocycle/cover lemmas are restated here from the
accepted `RationalTreePicardCoordinateCocycle` (same definitions, same proofs).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveLineCocycleRefinement

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.ProjectiveLinePicardExponent KltDP.Geometry.TransitionUnitExtraction

/-! ## The pulled-back cocycle (restated from the accepted `RationalTreePicardCoordinateCocycle`) -/

section PullbackUnits

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

theorem app_res {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    f.app V (res X h s) = res Y (f.preimage_le_preimage_of_le h) (f.app U s) := by
  have h1 := ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) s
  simp only [CommRingCat.comp_apply] at h1
  exact h1

theorem app_mul (U : X.Opens) (a b : Γ(X, U)) : f.app U (a * b) = f.app U a * f.app U b :=
  (f.app U).hom.map_mul a b

theorem app_one (U : X.Opens) : f.app U (1 : Γ(X, U)) = 1 :=
  (f.app U).hom.map_one

variable {ι : Type u} (U : ι → X.Opens) (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

theorem preimage_inf_le (i j : ι) : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ (U i ⊓ U j) :=
  fun _ hx => ⟨hx.1, hx.2⟩

/-- The pullback of a unit cocycle along a morphism. -/
def pullbackUnits (i j : ι) : Γ(Y, f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j)ˣ :=
  Units.map (res Y (preimage_inf_le f U i j)).toMonoidHom
    (Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom (g i j))

theorem pullbackUnits_val (i j : ι) :
    (pullbackUnits f U g i j : Γ(Y, f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j)) =
      res Y (preimage_inf_le f U i j) (f.app (U i ⊓ U j) (g i j)) := rfl

theorem pullbackUnits_isCocycle (hg : IsCocycle X U g) :
    IsCocycle Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) where
  unit_self i := by
    rw [pullbackUnits_val]
    have h : ((g i i : Γ(X, U i ⊓ U i))) = 1 := hg.unit_self i
    rw [h, app_one, map_one]
  mul_res i j l := by
    rw [pullbackUnits_val, pullbackUnits_val, pullbackUnits_val]
    simp only [res_res]
    have hT : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U l) :=
      fun _ hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2⟩
    have key : ∀ (a b : ι) (hab : U i ⊓ U j ⊓ U l ≤ U a ⊓ U b)
        (h : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U a ⊓ U b)),
        res Y h (f.app (U a ⊓ U b) (g a b)) =
          res Y hT (f.app (U i ⊓ U j ⊓ U l) (res X hab (g a b))) := by
      intro a b hab h
      rw [app_res, res_res]
    rw [key i j inf_le_left, key j l (inclCoc X U (U i) j l), key i l (inclSnd X U (U i) j l),
      ← map_mul, ← app_mul, hg.mul_res i j l]

theorem pullbackUnits_cover (hU : (⨆ i, U i) = ⊤) : (⨆ i, f ⁻¹ᵁ U i) = ⊤ :=
  f.preimage_iSup_eq_top hU

end PullbackUnits

/-- **The pullback compatibility of cocycle-glued line bundles** (lane A1's accepted
`pullbackGluedClass`, stated here on the restated `pullbackUnits`). -/
def PullbackGluedClass : Prop :=
  ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤),
    (pullbackInvertibleSheaf f (invertibleSheaf X U g hg hU)).toPic =
      picardClass Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) (pullbackUnits_isCocycle f U g hg)
        (pullbackUnits_cover f U hU)

/-! ## Classes of atlases -/

/-- The class of an invertible sheaf is the class of the transition cocycle of any atlas
(the accepted argument of lane A1's `toPic_eq_picardClass'`). -/
theorem toPic_eq_picardClass_atlas {X : Scheme.{u}} (L : InvertibleSheaf X)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (hU : (⨆ i, t.X i) = ⊤) :
    L.toPic = picardClass X t.X (transitionUnits X L.obj t) (transitionUnits_isCocycle X L.obj t) hU := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [picardClass_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨recoveryIso X L.obj t⟩

/-! ## Exponents on `P¹` -/

variable (k : Type u) [Field k]

/-- The glued line bundle of a standard-cover cocycle has that cocycle's exponent. -/
theorem exponent_invertibleSheaf
    (g : ∀ i j : ULift.{u} (Fin 2), Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤) :
    exponent k (invertibleSheaf (projectiveSpace k 1) (standardOpens k) g hg hU) =
      cocycleExponent k g :=
  exponent_eq_of_iso_to_glued k _ g hg (Iso.refl _)

/-- The Picard exponent of a standard-cover cocycle class. -/
theorem value_picardClass
    (g : ∀ i j : ULift.{u} (Fin 2), Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤) :
    value k (picardClass (projectiveSpace k 1) (standardOpens k) g hg hU) = cocycleExponent k g := by
  change value k (invertibleSheaf (projectiveSpace k 1) (standardOpens k) g hg hU).toPic = _
  rw [value_toPic, exponent_invertibleSheaf]

/-- A line bundle whose class is a standard-cover cocycle class has that cocycle's exponent. -/
theorem exponent_eq_cocycleExponent_of_toPic (L : InvertibleSheaf (projectiveSpace k 1))
    (g : ∀ i j : ULift.{u} (Fin 2), Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤)
    (h : L.toPic = picardClass (projectiveSpace k 1) (standardOpens k) g hg hU) :
    exponent k L = cocycleExponent k g := by
  rw [← value_toPic, h, value_picardClass]

/-- **Refinement to the standard cover**: the exponent of a line bundle whose class is a cocycle
class on a cover refined by the standard opens is the exponent of the refined cocycle. -/
theorem exponent_eq_of_refinement (L : InvertibleSheaf (projectiveSpace k 1)) {J : Type u}
    (U : J → (projectiveSpace k 1).Opens) (g : ∀ j j' : J, Γ(projectiveSpace k 1, U j ⊓ U j')ˣ)
    (hg : IsCocycle (projectiveSpace k 1) U g) (hU : (⨆ j, U j) = ⊤)
    (σ : ULift.{u} (Fin 2) → J) (hσ : ∀ i, standardOpens k i ≤ U (σ i))
    (h : L.toPic = picardClass (projectiveSpace k 1) U g hg hU) :
    exponent k L =
      cocycleExponent k (refinedUnits (projectiveSpace k 1) U g (standardOpens k) σ hσ) := by
  rw [← value_toPic, h,
    picardClass_eq_of_refinement (projectiveSpace k 1) U g hg (standardOpens k) σ hσ
      (standardCover k L),
    value_picardClass]

/-- **The exponent of a pulled-back glued line bundle**: for a section `s : P¹ ⟶ X` and a line bundle
`K` presented by a cocycle `g` on a cover `U` whose pullback is refined by the standard opens, given
the pullback compatibility `hP`. -/
theorem exponent_pullback_eq (hP : PullbackGluedClass.{u}) {X : Scheme.{u}} (K : InvertibleSheaf X)
    {J : Type u} (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ) (hg : IsCocycle X U g)
    (hU : (⨆ j, U j) = ⊤) (hK : K.toPic = picardClass X U g hg hU) (s : projectiveSpace k 1 ⟶ X)
    (σ : ULift.{u} (Fin 2) → J) (hσ : ∀ i, standardOpens k i ≤ s ⁻¹ᵁ U (σ i)) :
    exponent k (pullbackInvertibleSheaf s K) =
      cocycleExponent k (refinedUnits (projectiveSpace k 1) (fun j => s ⁻¹ᵁ U j)
        (pullbackUnits s U g) (standardOpens k) σ hσ) := by
  apply exponent_eq_of_refinement k _ (fun j => s ⁻¹ᵁ U j) (pullbackUnits s U g)
    (pullbackUnits_isCocycle s U g hg) (pullbackUnits_cover s U hU) σ hσ
  rw [← schemePicardPullbackHom_toPic, hK]
  change schemePicardPullbackHom s (invertibleSheaf X U g hg hU).toPic = _
  rw [schemePicardPullbackHom_toPic]
  exact hP s U g hg hU

/-- The same, as the Laurent exponent of the refined pulled-back transition unit. -/
theorem exponent_pullback_eq_overlapExponent (hP : PullbackGluedClass.{u}) {X : Scheme.{u}}
    (K : InvertibleSheaf X) {J : Type u} (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ)
    (hg : IsCocycle X U g) (hU : (⨆ j, U j) = ⊤) (hK : K.toPic = picardClass X U g hg hU)
    (s : projectiveSpace k 1 ⟶ X) (σ : ULift.{u} (Fin 2) → J)
    (hσ : ∀ i, standardOpens k i ≤ s ⁻¹ᵁ U (σ i)) :
    exponent k (pullbackInvertibleSheaf s K) =
      overlapExponent k (overlapRestriction k (refinedUnits (projectiveSpace k 1)
        (fun j => s ⁻¹ᵁ U j) (pullbackUnits s U g) (standardOpens k) σ hσ ⟨0⟩ ⟨1⟩)) :=
  exponent_pullback_eq k hP K U g hg hU hK s σ hσ

/-- **`exponent_of_frames`**: if the refined pulled-back transition unit reads `c · Tⁿ` in the Laurent
ring of the overlap, the exponent of the pulled-back bundle is `n`. -/
theorem exponent_pullback_eq_of_monomial (hP : PullbackGluedClass.{u}) {X : Scheme.{u}}
    (K : InvertibleSheaf X) {J : Type u} (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ)
    (hg : IsCocycle X U g) (hU : (⨆ j, U j) = ⊤) (hK : K.toPic = picardClass X U g hg hU)
    (s : projectiveSpace k 1 ⟶ X) (σ : ULift.{u} (Fin 2) → J)
    (hσ : ∀ i, standardOpens k i ≤ s ⁻¹ᵁ U (σ i)) (c : kˣ) (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (refinedUnits (projectiveSpace k 1)
        (fun j => s ⁻¹ᵁ U j) (pullbackUnits s U g) (standardOpens k) σ hσ ⟨0⟩ ⟨1⟩)) :
          (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    exponent k (pullbackInvertibleSheaf s K) = n := by
  rw [exponent_pullback_eq_overlapExponent k hP K U g hg hU hK s σ hσ]
  exact unitExponent_eq_of_monomial k _ c n h

end KltDP.Geometry.ProjectiveLineCocycleRefinement
