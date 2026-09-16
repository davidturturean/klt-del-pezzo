import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Schemes of finite type over a Noetherian affine base are locally Noetherian

For `f : X ⟶ Spec R` locally of finite type with `R` Noetherian, every affine open of `X` has a
section ring of finite type over `Γ(Spec R, ⊤) ≅ R` (Mathlib `HasRingHomProperty.appLE` for
`LocallyOfFiniteType`), hence Noetherian (Hilbert, `Algebra.FiniteType.isNoetherianRing`); so `X`
is locally Noetherian (`isLocallyNoetherian_of_locallyOfFiniteType_spec`). If moreover `f` is
quasi-compact (e.g. proper), `X` is a Noetherian scheme and a Noetherian space
(`isNoetherian_of_locallyOfFiniteType_quasiCompact_spec`,
`noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec`). Used for the multi-centre surface
`S_{p,n}`, which is proper over the field `k` (lane F's `multiStructure_isProper`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsNoetherianRing R]

/-- A scheme locally of finite type over the spectrum of a Noetherian ring is locally
Noetherian. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType_spec [LocallyOfFiniteType f] :
    IsLocallyNoetherian X := by
  refine ⟨fun V => ?_⟩
  let g : Γ(Spec R, ⊤) ⟶ Γ(X, V.1) := f.appLE ⊤ V.1 (fun x _ => trivial)
  have hft : RingHom.FiniteType g.hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹LocallyOfFiniteType f›
      ⟨⊤, isAffineOpen_top (Spec R)⟩ V (fun x _ => trivial)
  haveI hN : IsNoetherianRing Γ(Spec R, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
  letI : Algebra Γ(Spec R, ⊤) Γ(X, V.1) := g.hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Spec R, ⊤) Γ(X, V.1) := hft
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec R, ⊤) Γ(X, V.1)

/-- A scheme of finite type and quasi-compact over the spectrum of a Noetherian ring is a
Noetherian scheme. -/
theorem isNoetherian_of_locallyOfFiniteType_quasiCompact_spec [LocallyOfFiniteType f]
    [QuasiCompact f] : IsNoetherian X := by
  haveI : CompactSpace (Spec R) := inferInstanceAs (CompactSpace (PrimeSpectrum R))
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_spec f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- Its underlying space is Noetherian. -/
theorem noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec [LocallyOfFiniteType f]
    [QuasiCompact f] : NoetherianSpace X :=
  haveI := isNoetherian_of_locallyOfFiniteType_quasiCompact_spec f
  inferInstance

/-- Universe check at universe `0`. -/
example {X₀ : Scheme.{0}} {R₀ : CommRingCat.{0}} (f₀ : X₀ ⟶ Spec R₀) [IsNoetherianRing R₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] : NoetherianSpace X₀ :=
  noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec f₀

end KltDP.Geometry
