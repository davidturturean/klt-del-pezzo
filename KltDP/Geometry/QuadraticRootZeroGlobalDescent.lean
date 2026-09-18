import KltDP.Geometry.QuadraticRootZeroBaseClosedImmersion

/-!
# Descent of original root-zero chart maps into a closed base subscheme

An abstract original atlas isolates the gluing and its projection/range
proofs from the concrete Cartier sheaf recovery. Original chart triangles
give compatibility after a monomorphism to the base. Their exact ranges
give surjectivity, and the proved original base closed immersion gives
closedness of the descended factor.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

variable {X Z : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
    (b : Z ⟶ X) [Mono b] (f : ∀ i, D.rootZeroChart i ⟶ Z)
    (hf : ∀ i, f i ≫ b = D.rootZeroChartToBase i)

/-- The original base-compatible chart maps glue to the original global root-zero scheme. -/
def rootZeroGlobalDesc : D.rootZeroGlobalScheme ⟶ Z := by
  refine D.rootZeroGlueData.openCover.glueMorphisms f ?_
  intro i j
  apply (cancel_mono b).mp
  rw [Category.assoc, Category.assoc, hf i, hf j]
  rw [← D.rootZeroGlobalChartι_toBase i, ← D.rootZeroGlobalChartι_toBase j]
  simpa only [Category.assoc] using
    (pullback.condition_assoc (f := D.rootZeroGlobalChartι i)
      (g := D.rootZeroGlobalChartι j) (D.rootZeroGlobalι ≫ D.morphism))

@[reassoc]
theorem rootZeroGlobalChartι_desc (i : ι) :
    D.rootZeroGlobalChartι i ≫ D.rootZeroGlobalDesc b f hf = f i := by
  dsimp only [rootZeroGlobalDesc, rootZeroGlobalChartι]
  exact D.rootZeroGlueData.openCover.ι_glueMorphisms f _ i

@[reassoc]
theorem rootZeroGlobalDesc_toBase :
    D.rootZeroGlobalDesc b f hf ≫ b = D.rootZeroGlobalι ≫ D.morphism := by
  apply D.rootZeroGlueData.openCover.hom_ext
  intro i
  change D.rootZeroGlobalChartι i ≫ (D.rootZeroGlobalDesc b f hf ≫ b) =
    D.rootZeroGlobalChartι i ≫ (D.rootZeroGlobalι ≫ D.morphism)
  rw [← Category.assoc, rootZeroGlobalChartι_desc, hf i, rootZeroGlobalChartι_toBase]

theorem rootZeroGlobalDesc_isClosedImmersion [IsClosedImmersion b] :
    IsClosedImmersion (D.rootZeroGlobalDesc b f hf) := by
  letI : IsClosedImmersion (D.rootZeroGlobalDesc b f hf ≫ b) := by
    rw [rootZeroGlobalDesc_toBase]
    exact D.rootZeroGlobal_toBase_isClosedImmersion
  exact IsClosedImmersion.of_comp_isClosedImmersion _ b

/-- Exact original chart ranges imply surjectivity of the actual descended map. -/
theorem rootZeroGlobalDesc_surjective
    (hr : ∀ i, Set.range (f i).base = b.base ⁻¹' (D.opens i : Set X)) :
    Surjective (D.rootZeroGlobalDesc b f hf) := by
  constructor
  intro y
  have hy : b.base y ∈ ⨆ i, D.opens i := by rw [D.covers]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  have hi' : y ∈ Set.range (f i).base := by rw [hr i]; exact hi
  obtain ⟨z, hz⟩ := hi'
  refine ⟨(D.rootZeroGlobalChartι i).base z, ?_⟩
  change (D.rootZeroGlobalChartι i ≫ D.rootZeroGlobalDesc b f hf).base z = y
  rwa [rootZeroGlobalChartι_desc]

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobalDesc_toBase
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobalDesc_isClosedImmersion
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobalDesc_surjective
