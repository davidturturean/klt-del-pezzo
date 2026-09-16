import KltDP.Geometry.ModuleCohomologyConnectingLinear
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension identities from the actual cohomology sequence

The linear maps below are the coefficient maps of `baseFunctor` and the
existing connecting map. Their exactness is derived from the actual
scheme-module long exact sequence. Rank-nullity then gives the dimension
recurrence, with the connecting-map image recording the boundary term.
Finite-dimensionality is explicit; no numerical Euler identity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The connecting map bundled between the original base-cohomology modules. -/
def baseConnectingArrow (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    (baseFunctor f n).obj S.X₃ ⟶ (baseFunctor f (n + 1)).obj S.X₁ := by
  letI := baseModule f S.X₃ n
  letI := baseModule f S.X₁ (n + 1)
  exact ModuleCat.ofHom (connectingBaseLinearMap f S hS n)

/-- Exactness at the middle cohomology module, for the actual linear maps. -/
theorem baseExact_middle (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((baseFunctor f n).map S.f).hom
      ((baseFunctor f n).map S.g).hom := by
  intro x
  constructor
  · intro hx
    exact exact_middle S hS n x hx
  · rintro ⟨y, rfl⟩
    exact CategoryTheory.Sheaf.H.longSequence_comp_zero₂
      (S := S.map (SheafOfModules.toSheaf X.ringCatSheaf)) n y

/-- Exactness immediately before the original linear connecting map. -/
theorem baseExact_before_connecting
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((baseFunctor f n).map S.g).hom
      (baseConnectingArrow f S hS n).hom := by
  intro x
  constructor
  · intro hx
    exact exact_before_connecting S hS n x hx
  · rintro ⟨y, rfl⟩
    exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃
      (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl y

/-- Exactness immediately after the original linear connecting map. -/
theorem baseExact_after_connecting
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (baseConnectingArrow f S hS n).hom
      ((baseFunctor f (n + 1)).map S.f).hom := by
  intro x
  constructor
  · intro hx
    exact exact_after_connecting S hS n x hx
  · rintro ⟨y, rfl⟩
    exact CategoryTheory.Sheaf.H.longSequence_comp_zero₁
      (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl y

/-- The initial cohomology map is injective because it is the actual map
on global sections of a monomorphism of module sheaves. -/
theorem baseMap_zero_injective
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    Function.Injective ((baseFunctor f 0).map S.f).hom := by
  letI : Mono S.f := hS.mono_f
  let E := SheafOfModules.evaluation X.ringCatSheaf (.op (⊤ : Opens X))
  haveI : Mono (E.map S.f) := by
    dsimp only [E]
    infer_instance
  have he : Function.Injective (S.f.val.app (.op (⊤ : Opens X))) :=
    (ModuleCat.mono_iff_injective (E.map S.f)).mp inferInstance
  intro x y hxy
  apply (hZeroEquivGlobalSections S.X₁).injective
  apply he
  rw [hZeroEquivGlobalSections_naturality, hZeroEquivGlobalSections_naturality]
  exact congrArg (hZeroEquivGlobalSections S.X₂) hxy

/-- Dimension of the existing cohomology module over the original field. -/
def cohomologyDimension (M : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k ((baseFunctor f n).obj M)

/-- Dimension of the actual connecting-map image. -/
def connectingRank (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) : ℕ :=
  Module.finrank k (LinearMap.range (baseConnectingArrow f S hS n).hom)

/-- Rank-nullity at the three actual terms, with the first kernel retained
as a boundary term. -/
theorem cohomology_dimension_rank_identity
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k ((baseFunctor f n).obj S.X₁)]
    [FiniteDimensional k ((baseFunctor f n).obj S.X₂)]
    [FiniteDimensional k ((baseFunctor f n).obj S.X₃)] :
    (cohomologyDimension f S.X₁ n : ℤ) - cohomologyDimension f S.X₂ n +
        cohomologyDimension f S.X₃ n =
      Module.finrank k (LinearMap.ker ((baseFunctor f n).map S.f).hom) +
        (connectingRank f S hS n : ℤ) := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker ((baseFunctor f n).map S.f).hom
  have h₂ := LinearMap.finrank_range_add_finrank_ker ((baseFunctor f n).map S.g).hom
  have h₃ := LinearMap.finrank_range_add_finrank_ker (baseConnectingArrow f S hS n).hom
  rw [LinearMap.exact_iff.mp (baseExact_middle f S hS n)] at h₂
  rw [LinearMap.exact_iff.mp (baseExact_before_connecting f S hS n)] at h₃
  dsimp only [cohomologyDimension, connectingRank]
  omega

/-- Degree zero has no incoming cohomology boundary. -/
theorem cohomology_dimension_rank_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [FiniteDimensional k ((baseFunctor f 0).obj S.X₁)]
    [FiniteDimensional k ((baseFunctor f 0).obj S.X₂)]
    [FiniteDimensional k ((baseFunctor f 0).obj S.X₃)] :
    (cohomologyDimension f S.X₁ 0 : ℤ) - cohomologyDimension f S.X₂ 0 +
        cohomologyDimension f S.X₃ 0 = (connectingRank f S hS 0 : ℤ) := by
  have h := cohomology_dimension_rank_identity f S hS 0
  rw [LinearMap.ker_eq_bot.mpr (baseMap_zero_injective f S hS)] at h
  simpa using h

/-- In positive degree the preceding connecting image is exactly the
first kernel; this is the dimension recurrence used by Euler cancellation. -/
theorem cohomology_dimension_rank_succ
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k ((baseFunctor f (n + 1)).obj S.X₁)]
    [FiniteDimensional k ((baseFunctor f (n + 1)).obj S.X₂)]
    [FiniteDimensional k ((baseFunctor f (n + 1)).obj S.X₃)] :
    (cohomologyDimension f S.X₁ (n + 1) : ℤ) - cohomologyDimension f S.X₂ (n + 1) +
        cohomologyDimension f S.X₃ (n + 1) =
      (connectingRank f S hS n : ℤ) + connectingRank f S hS (n + 1) := by
  have h := cohomology_dimension_rank_identity f S hS (n + 1)
  rw [LinearMap.exact_iff.mp (baseExact_after_connecting f S hS n)] at h
  exact h

/-- Vanishing of the next first cohomology group kills the last connecting
image, giving the upper boundary needed for a finite Euler sum. -/
theorem connectingRank_eq_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (H S.X₁ (n + 1))] : connectingRank f S hS n = 0 := by
  haveI : Subsingleton ((baseFunctor f (n + 1)).obj S.X₁) :=
    inferInstanceAs (Subsingleton (H S.X₁ (n + 1)))
  dsimp only [connectingRank]
  exact Module.finrank_zero_of_subsingleton

end KltDP.Geometry.ModuleCohomology
