import KltDP.Geometry.InvertibleSectionNonvanishingCompact
import KltDP.Geometry.InvertibleSectionNonvanishingFrame
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import KltDP.Geometry.InvertibleSheafFrameSectionExtension
import KltDP.Geometry.QuasicoherentOpenRestriction

/-!
# Actual finite affine extensions with a common power

Starting with an original invertible sheaf, its original section, and an
original quasicoherent section on its nonvanishing open, construct a finite
affine frame cover and a single exponent after which every chart has a
twisted extension. The chart frames come from the actual original atlas;
the chart input is the original pulled section on the proved preimage open.

The finite maximum and all local lifts are constructed. Their agreement on
overlaps and their global gluing remain the next step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFiniteAffineExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance finiteAffineExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSectionNonvanishingOpen InvertibleSectionNonvanishingCompact
open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- Indices of the original affine refinement of the original atlas. -/
abbrev Chart := AffineOpenRefinement.Index X L.localTrivializations.X

/-- The original subordinate affine open indexed by a refinement chart. -/
def chartOpen (a : Chart L) : X.Opens :=
  AffineOpenRefinement.opens X L.localTrivializations.X a

/-- The actual invertible sheaf pulled to this original open subscheme. -/
abbrev chartLine (a : Chart L) : InvertibleSheaf (chartOpen L a).toScheme :=
  pullbackInvertibleSheaf (chartOpen L a).ι L

/-- The actual original module pulled to this original open subscheme. -/
abbrev chartModule (M : X.Modules) (a : Chart L) : (chartOpen L a).toScheme.Modules :=
  (schemeModulePullback (chartOpen L a).ι).obj M

/-- The actual Over-site frame, transported by the proved original
open-to-Over and restriction-to-pullback comparisons. -/
def chartFrame (a : Chart L) :
    (chartLine L a).obj ≅ _root_.SheafOfModules.unit (chartOpen L a).toScheme.ringCatSheaf :=
  chartPullbackUnitIsoOf (chartOpen L a) L.obj
    (refinementFrame X L.obj L.localTrivializations a).symm

/-- The literal compatible-section pullback of the original line section. -/
def chartSection (s : L.obj.sections) (a : Chart L) : (chartLine L a).obj.sections :=
  InvertibleSheafSectionPowersPullback.pullbackSection (chartOpen L a).ι L.obj s

/-- The original coefficient in the actual affine frame. -/
def chartCoefficient (s : L.obj.sections) (a : Chart L) : Γ((chartOpen L a).toScheme, ⊤) :=
  frameCoefficient (chartLine L a) (chartFrame L a) (chartSection L s a)

/-- The coefficient basic open is the actual preimage of the original
nonvanishing open; no open-comparison hypothesis is supplied. -/
theorem chartBasicOpen_eq (s : L.obj.sections) (a : Chart L) :
    (chartOpen L a).toScheme.basicOpen (chartCoefficient L s a) =
      (chartOpen L a).ι ⁻¹ᵁ nonvanishingOpen X L s := by
  calc
    _ = nonvanishingOpen (chartOpen L a).toScheme (chartLine L a)
        (chartSection L s a) :=
      (InvertibleSectionNonvanishingFrame.nonvanishingOpen_eq_basicOpen
        (chartLine L a) (chartFrame L a) (chartSection L s a)).symm
    _ = _ := InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
      (chartOpen L a).ι L s

/-- The given original section, pulled to the affine chart and transported
along the proved equality of its actual nonvanishing opens. -/
def localSection (M : X.Modules) (s : L.obj.sections)
    (t : M.val.obj (op (nonvanishingOpen X L s))) (a : Chart L) :
    (chartModule L M a).val.obj
      (op ((chartOpen L a).toScheme.basicOpen (chartCoefficient L s a))) :=
  (chartModule L M a).val.map (eqToHom (chartBasicOpen_eq L s a)).op
    (RationalTreePicard.pulledSection (chartOpen L a).ι M (nonvanishingOpen X L s) t)

private theorem isQuasicoherent_chartModule (M : X.Modules) [M.IsQuasicoherent]
    (a : Chart L) : (chartModule L M a).IsQuasicoherent :=
  _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := (chartOpen L a).toScheme.ringCatSheaf)
    (M := (SchemeModuleRestriction.restriction (chartOpen L a).ι).obj M)
    (N := chartModule L M a)
    ((SchemeModuleRestriction.restrictionIsoPullback (chartOpen L a).ι).hom.app M)

private theorem eventually_exists_on_chart (M : X.Modules) [M.IsQuasicoherent]
    (s : L.obj.sections) (t : M.val.obj (op (nonvanishingOpen X L s)))
    (a : Chart L) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.obj (op ⊤),
        (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.map
            (homOfLE ((chartOpen L a).toScheme.basicOpen_le
              (chartCoefficient L s a))).op v =
          (rightTwistMap (chartModule L M a) (chartLine L a)
            (chartSection L s a) n).val.app
              (op ((chartOpen L a).toScheme.basicOpen (chartCoefficient L s a)))
            (localSection L M s t a) := by
  letI : IsAffine (chartOpen L a).toScheme :=
    AffineOpenRefinement.affine X L.localTrivializations.X a
  letI : (chartModule L M a).IsQuasicoherent := isQuasicoherent_chartModule L M a
  exact InvertibleSheafFrameSectionExtension.eventually_exists_twisted_extension
    (chartModule L M a) (chartLine L a) isCompact_univ isQuasiSeparated_univ
    (chartFrame L a) (chartSection L s a) (localSection L M s t a)

private theorem uniform_eventually_of_finite {I : Type u} [Finite I]
    (P : I → ℕ → Prop) (hP : ∀ i, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P i n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i, P i n := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  choose N hN using hP
  refine ⟨Finset.univ.sup N, fun n hn i => hN i n ?_⟩
  exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn

private theorem finite_cover_uniform_eventually {A : Type u}
    (U : A → X.Opens) (P : A → ℕ → Prop)
    (hc : ∃ S : Finset A, (⨆ a : S, U a.val) = ⊤)
    (hP : ∀ a, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P a n) :
    ∃ S : Finset A, (⨆ a : S, U a.val) = ⊤ ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : S, P a.val n := by
  obtain ⟨S, hS⟩ := hc
  exact ⟨S, hS, uniform_eventually_of_finite (fun a : S => P a.val) (fun a => hP a.val)⟩

/-- A finite actual affine cover and a common power threshold for all its
actual twisted lifts. Neither frames, exponents nor lift families are inputs. -/
theorem eventually_exists_on_finite_affine_cover (M : X.Modules) [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X)) (s : L.obj.sections)
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ S : Finset (Chart L), (⨆ a : S, chartOpen L a.val) = ⊤ ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : S,
        ∃ v : (chartModule L M a.val ⊗ (power (chartLine L a.val) n).obj).val.obj (op ⊤),
          (chartModule L M a.val ⊗ (power (chartLine L a.val) n).obj).val.map
              (homOfLE ((chartOpen L a.val).toScheme.basicOpen_le
                (chartCoefficient L s a.val))).op v =
            (rightTwistMap (chartModule L M a.val) (chartLine L a.val)
              (chartSection L s a.val) n).val.app
                (op ((chartOpen L a.val).toScheme.basicOpen (chartCoefficient L s a.val)))
              (localSection L M s t a.val) := by
  apply finite_cover_uniform_eventually (chartOpen L)
    (fun a n => ∃ v : (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.obj (op ⊤),
      (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.map
          (homOfLE ((chartOpen L a).toScheme.basicOpen_le (chartCoefficient L s a))).op v =
        (rightTwistMap (chartModule L M a) (chartLine L a) (chartSection L s a) n).val.app
          (op ((chartOpen L a).toScheme.basicOpen (chartCoefficient L s a)))
          (localSection L M s t a))
    (exists_finite_affine_refinement X L.obj L.localTrivializations hX)
  exact eventually_exists_on_chart L M s t

end KltDP.Geometry.InvertibleSheafFiniteAffineExtension
