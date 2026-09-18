import KltDP.Geometry.FiniteProjectiveChartGenerators
import KltDP.Geometry.PowerSectionFunctionExtension
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.InvertibleSectionNonvanishingPowers

/-!
# A common original power clears all finite projective-chart generators

The actual finite preimage charts supply finitely many original algebra
generators. Their denominators are powers of the actual pulled homogeneous
sections. The existing extension theorem and a finite maximum produce one
positive exponent and actual global sections with literal chart equations.
The original power-coordinate sections cover the original finite source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteProjectivePowerGenerators

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance powerGeneratorsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance sectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open FiniteProjectiveChartGenerators ProjectiveSpaceDegreeOneSheaf
  ProjectiveCoordinateSectionBasicOpen InvertibleSectionNonvanishingOpen
  InvertibleSheafSectionPowers PowerSectionFunctionExtension

variable {k : Type u} [Field k] {n : ℕ} {Y Z : Scheme.{u}}
  (π : Z ⟶ Y) (i : Y ⟶ projectiveSpace k n)

/-- The actual degree-one line pulled through the original composite. -/
abbrev line : InvertibleSheaf Z := pullbackInvertibleSheaf (π ≫ i) (degreeOne k n)

/-- The original compatible homogeneous-coordinate sections after pullback. -/
def coordinateSection (j : Fin (n + 1)) : (line π i).obj.sections :=
  InvertibleSheafSectionPowersPullback.pullbackSection (π ≫ i) (degreeOne k n).obj
    (homogeneousSection k n j)

/-- Their intrinsic nonvanishing opens are the literal original preimage charts. -/
theorem nonvanishing_coordinateSection (j : Fin (n + 1)) :
    nonvanishingOpen Z (line π i) (coordinateSection π i j) = chartOpen π i j := by
  dsimp only [coordinateSection, line]
  rw [InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback,
    nonvanishingOpen_homogeneousSection]

/-- These original section opens cover, for every original composite map. -/
theorem coordinateSections_cover :
    (⨆ j, nonvanishingOpen Z (line π i) (coordinateSection π i j)) = ⊤ := by
  calc
    _ = ⨆ j, (π ≫ i) ⁻¹ᵁ standardOpen k n j :=
      iSup_congr (nonvanishing_coordinateSection π i)
    _ = (π ≫ i) ⁻¹ᵁ (⨆ j, standardOpen k n j) :=
      ((π ≫ i).preimage_iSup (standardOpen k n)).symm
    _ = ⊤ := by rw [ProjectiveChart.iSup_coordinateStandardOpen]; rfl

/-- Original positive power-coordinate sections retain that same cover. -/
theorem powerCoordinateSections_cover {q : ℕ} (hq : 0 < q) :
    (⨆ j, nonvanishingOpen Z (power (line π i) q)
      (powerSection (line π i) (coordinateSection π i j) q)) = ⊤ := by
  calc
    _ = ⨆ j, nonvanishingOpen Z (line π i) (coordinateSection π i j) :=
      iSup_congr (fun j =>
        InvertibleSectionNonvanishingPowers.nonvanishingOpen_power
          (line π i) (coordinateSection π i j) hq)
    _ = ⊤ := coordinateSections_cover π i

private theorem extension_on_equal_open {X : Scheme.{u}}
    (L : InvertibleSheaf X) (s : L.obj.sections)
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (U : X.Opens) (hU : U = nonvanishingOpen X L s) (b : Γ(X, U)) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → ∃ t : (power L q).obj.sections,
      sectionValue (power L q).obj t U =
        b • sectionValue (power L q).obj (powerSection L s q) U := by
  subst U
  exact eventually_exists_power_extension L s hX hXqs b

variable [IsFinite π] [IsClosedImmersion i]

/-- One actual positive tensor power simultaneously clears all the chosen
original finite chart generators, with their original scalar surjections. -/
theorem exists_common_power_generators :
    ∃ (q : ℕ), 0 < q ∧ ∃ (r : Fin (n + 1) → ℕ)
      (b : ∀ j, Fin (r j) → Γ(Z, chartOpen π i j))
      (t : ∀ j, Fin (r j) → (power (line π i) q).obj.sections),
      (∀ j, Function.Surjective (MvPolynomial.eval₂Hom (chartScalars π i j) (b j))) ∧
      (∀ j a, sectionValue (power (line π i) q).obj (t j a) (chartOpen π i j) =
        b j a • sectionValue (power (line π i) q).obj
          (powerSection (line π i) (coordinateSection π i j) q) (chartOpen π i j)) := by
  classical
  letI : NoetherianSpace (projectiveSpace k n) := projectiveSpace_noetherianSpace k n
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ i)
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ i)
  choose r b hb using (fun j : Fin (n + 1) => exists_chart_generators π i j)
  have hext (j : Fin (n + 1)) (a : Fin (r j)) :
      ∃ N : ℕ, ∀ q : ℕ, N ≤ q → ∃ t : (power (line π i) q).obj.sections,
        sectionValue (power (line π i) q).obj t (chartOpen π i j) =
          b j a • sectionValue (power (line π i) q).obj
            (powerSection (line π i) (coordinateSection π i j) q) (chartOpen π i j) :=
    extension_on_equal_open (line π i) (coordinateSection π i j)
      isCompact_univ isQuasiSeparated_univ (chartOpen π i j)
      (nonvanishing_coordinateSection π i j).symm (b j a)
  choose threshold extend using hext
  let q : ℕ := Finset.univ.sup
    (fun a : (j : Fin (n + 1)) × Fin (r j) => threshold a.1 a.2) + 1
  have hbound (j : Fin (n + 1)) (a : Fin (r j)) : threshold j a ≤ q := by
    exact (Finset.le_sup
      (f := fun a : (j : Fin (n + 1)) × Fin (r j) => threshold a.1 a.2)
      (Finset.mem_univ ⟨j, a⟩)).trans (Nat.le_succ _)
  have hextq (j : Fin (n + 1)) (a : Fin (r j)) :
      ∃ t : (power (line π i) q).obj.sections,
        sectionValue (power (line π i) q).obj t (chartOpen π i j) =
          b j a • sectionValue (power (line π i) q).obj
            (powerSection (line π i) (coordinateSection π i j) q) (chartOpen π i j) :=
    extend j a q (hbound j a)
  choose t ht using hextq
  exact ⟨q, Nat.succ_pos _, r, b, t, hb, ht⟩

end KltDP.Geometry.FiniteProjectivePowerGenerators
