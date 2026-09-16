import KltDP.Geometry.AffineBlowupExceptional
import KltDP.Geometry.GluedIdealKernelTrivialization

/-!
# Actual local exceptional-kernel and conormal trivializations

The regular principal equations on the actual Rees-chart cover were
proved from the original center ideal. They now give isomorphisms of
actual module sheaves for the corresponding restricted exceptional
closed immersions. No integrality or nonzero-center hypothesis is used.

The comparison with restriction of the global exceptional kernel and
conormal sheaves remains a separate functorial base-change theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Every point of the actual affine blowup has an affine neighborhood
on which the kernel of the restricted exceptional immersion is trivial,
and its actual conormal on the inverse image is trivial. The isomorphisms
come from the proved regular equation of the original center. -/
theorem exists_exceptional_kernel_conormal_trivializations (x : scheme I) :
    ∃ U : (scheme I).affineOpens, x ∈ U.1 ∧
      Nonempty (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf ≅
        schemeKernelIdeal ((exceptionalι I) ∣_ U.1)) ∧
      Nonempty (_root_.SheafOfModules.unit
          ((exceptionalι I) ⁻¹ᵁ U.1).toScheme.ringCatSheaf ≅
        schemeConormalSheaf ((exceptionalι I) ∣_ U.1)) := by
  obtain ⟨U, hx, d, hI, hregular⟩ := exceptionalIdeal_locallyPrincipalRegular I x
  exact ⟨U, hx,
    ⟨gluedAffineKernelIso (exceptionalIdeal I) U d hI hregular⟩,
    ⟨gluedAffineConormalIso (exceptionalIdeal I) U d hI hregular⟩⟩

/-- In particular, both actual sheaves attached to each restricted
exceptional immersion are locally free of rank one on this chart. -/
theorem exists_exceptional_kernel_conormal_invertible (x : scheme I) :
    ∃ U : (scheme I).affineOpens, x ∈ U.1 ∧
      KltDP.SheafOfModules.IsInvertible (R := U.1.toScheme.ringCatSheaf)
        (schemeKernelIdeal ((exceptionalι I) ∣_ U.1)) ∧
      KltDP.SheafOfModules.IsInvertible
        (R := ((exceptionalι I) ⁻¹ᵁ U.1).toScheme.ringCatSheaf)
        (schemeConormalSheaf ((exceptionalι I) ∣_ U.1)) := by
  obtain ⟨U, hx, d, hI, hregular⟩ := exceptionalIdeal_locallyPrincipalRegular I x
  exact ⟨U, hx,
    gluedAffineKernel_isInvertible (exceptionalIdeal I) U d hI hregular,
    gluedAffineConormal_isInvertible (exceptionalIdeal I) U d hI hregular⟩

end KltDP.Geometry.AffineBlowup
