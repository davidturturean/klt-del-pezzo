import KltDP.Geometry.InvertibleSheafSectionExtension
import KltDP.Geometry.SchemeStructureTensorLeft

/-!
# Original functions extend after multiplying by an original section power

The existing QCQS extension theorem is specialized to the actual structure
module. The original left structure action removes the unit tensor factor.
Its comparison with the original right action is proved by unitor naturality,
so the final equation is literal scalar multiplication by the power section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.PowerSectionFunctionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance powerExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance sectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
  InvertibleSectionNonvanishingOpen

/-- Evaluate the original compatible family, retaining its actual module carrier. -/
abbrev sectionValue {X : Scheme.{u}} (M : X.Modules) (s : M.sections) (U : X.Opens) :
    M.val.obj (op U) := s.val (op U)

private theorem transported_unit_mul_eq_left
    {C : Type*} [Category C] [MonoidalCategory C] {O : C} (e : 𝟙_ C ≅ O) :
    O ◁ e.inv ≫ (ρ_ O).hom = e.inv ▷ O ≫ (λ_ O).hom := by
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc]
  rw [← rightUnitor_naturality, ← leftUnitor_naturality,
    whisker_exchange_assoc, unitors_equal]

private theorem transported_unit_map
    {C : Type*} [Category C] [MonoidalCategory C] {O N : C}
    (e : 𝟙_ C ≅ O) (g : O ⟶ N) :
    (𝟙 O ⊗ g) ≫ (e.inv ▷ N ≫ (λ_ N).hom) =
      (O ◁ e.inv ≫ (ρ_ O).hom) ≫ g := by
  rw [transported_unit_mul_eq_left]
  simp only [tensorHom_def, id_whiskerRight, Category.id_comp]
  rw [whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]

/-- The actual unit-coefficient twist becomes the original power-section map
under the original left structure-module action. -/
theorem rightTwistMap_unit_comp_leftIso {X : Scheme.{u}}
    (L : InvertibleSheaf X) (s : L.obj.sections) (n : ℕ) :
    rightTwistMap (_root_.SheafOfModules.unit X.ringCatSheaf) L s n ≫
        (schemeStructureTensorLeftIso (power L n).obj).hom = powerSectionHom L s n := by
  let O := _root_.SheafOfModules.unit X.ringCatSheaf
  let e : 𝟙_ X.Modules ≅ O :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  have h : (𝟙 O ⊗ powerSectionHom L s n) ≫
      (schemeStructureTensorLeftIso (power L n).obj).hom =
      (schemeStructureTensorRightIso O).hom ≫ powerSectionHom L s n := by
    change (𝟙 O ⊗ powerSectionHom L s n) ≫
      (e.inv ▷ (power L n).obj ≫ (λ_ (power L n).obj).hom) =
      (O ◁ e.inv ≫ (ρ_ O).hom) ≫ powerSectionHom L s n
    exact transported_unit_map e (powerSectionHom L s n)
  rw [rightTwistMap, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- An original regular function on D(s) is a quotient of an original
section of every sufficiently high power by that same power of s. -/
theorem eventually_exists_power_extension {X : Scheme.{u}}
    (L : InvertibleSheaf X) (s : L.obj.sections)
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (b : Γ(X, nonvanishingOpen X L s)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ t : (power L n).obj.sections,
      sectionValue (power L n).obj t (nonvanishingOpen X L s) =
        b • sectionValue (power L n).obj (powerSection L s n) (nonvanishingOpen X L s) := by
  let O := _root_.SheafOfModules.unit X.ringCatSheaf
  obtain ⟨N, hN⟩ := InvertibleSheafSectionExtension.eventually_exists_twisted_extension
    L O s hX hXqs b
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨v, hv⟩ := hN n hn
  let M := (power L n).obj
  let e : O ⊗ M ≅ M := schemeStructureTensorLeftIso M
  let t : M.sections := schemeModuleSectionOfTop M (e.hom.val.app (op ⊤) v)
  refine ⟨t, ?_⟩
  let U := nonvanishingOpen X L s
  have hnat : M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (e.hom.val.app (op ⊤) v) =
      e.hom.val.app (op U)
        ((O ⊗ M).val.map (homOfLE (show U ≤ ⊤ from le_top)).op v) :=
    (PresheafOfModules.naturality_apply e.hom.val
      (homOfLE (show U ≤ ⊤ from le_top)).op v).symm
  have hmap : e.hom.val.app (op U) ((rightTwistMap O L s n).val.app (op U) b) =
      (powerSectionHom L s n).val.app (op U) b :=
    congrArg (fun g : O ⟶ M => g.val.app (op U) b)
      (rightTwistMap_unit_comp_leftIso L s n)
  change M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (e.hom.val.app (op ⊤) v) =
    b • (powerSectionHom L s n).val.app (op U) (1 : Γ(X, U))
  rw [hnat, hv, hmap]
  simpa only [smul_eq_mul, mul_one] using
    ((powerSectionHom L s n).val.app (op U)).hom.map_smul b (1 : Γ(X, U))

end KltDP.Geometry.PowerSectionFunctionExtension
