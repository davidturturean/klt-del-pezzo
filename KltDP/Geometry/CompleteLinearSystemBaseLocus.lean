import KltDP.Geometry.CompleteLinearSystemExpansion
import KltDP.Geometry.SectionCombinationNonvanishing
import KltDP.Geometry.FiniteNonvanishingGenerators

/-!
# The whole H0 basis detects nonvanishing of every original global section

The exact basis expansion and local-ring nonvanishing lemma show that
each section's nonvanishing open lies in that of the complete system.
Consequently global generation makes this exact whole basis basepoint-free.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.CompleteLinearSystemExpansion

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open CompleteLinearSystemSections SectionLinearCombinations
  InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] (hpos : 0 < dimension f L)

/-- Every original global section is nonvanishing only inside the actual
non-base open of the entire original H0 basis. -/
theorem nonvanishingOpen_le_basis (s : L.obj.sections) :
    nonvanishingOpen X L s ≤
      ⨆ i, nonvanishingOpen X L (positiveBasisSections f L hpos i) := by
  calc
    nonvanishingOpen X L s = nonvanishingOpen X L
        (combination f L.obj (positiveBasisSections f L hpos)
          (coefficients f L hpos s)) :=
      congrArg (nonvanishingOpen X L) (combination_coefficients f L hpos s).symm
    _ ≤ _ := nonvanishingOpen_combination_le f L
      (positiveBasisSections f L hpos) (coefficients f L hpos s)

/-- If the original sheaf is globally generated, its entire H0 basis
has an actual nonvanishing cover of the whole original scheme. -/
theorem basis_cover_of_globallyGenerated (hL : Positivity.IsGloballyGenerated L.obj) :
    (⨆ i, nonvanishingOpen X L (positiveBasisSections f L hpos i)) = ⊤ := by
  obtain ⟨I, g, hg⟩ := hL
  letI := hg
  let G := (_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi g
  apply top_unique
  intro x hx
  obtain ⟨j, hj⟩ := FiniteNonvanishingGenerators.exists_mem_nonvanishing L G x
  exact nonvanishingOpen_le_basis f L hpos (G.s j) hj

end KltDP.Geometry.CompleteLinearSystemExpansion
