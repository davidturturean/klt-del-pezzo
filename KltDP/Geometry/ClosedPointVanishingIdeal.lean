import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.SchematicImageDenseOpen

/-! The actual reduced closed-point ideal, on and off its original point.
These computations retain the original affine section rings and identify
the kernel of the canonical rational point section with that same ideal. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ClosedPointVanishingIdeal

variable (X : Scheme.{u}) (x : X) (hclosed : IsClosed ({x} : Set X))

/-- The existing vanishing ideal of the actual closed singleton. -/
def ideal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hclosed⟩

/-- On an original affine neighborhood, this is the prime of the same point. -/
theorem ideal_eq_prime (U : X.affineOpens) (hx : x ∈ U.1) :
    (ideal X x hclosed).ideal U = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hpre : U.2.fromSpec.base ⁻¹' ({x} : Set X) = {U.2.primeIdealOf ⟨x, hx⟩} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp
      exact U.2.fromSpec.isOpenEmbedding.injective
        (hp.trans (U.2.fromSpec_primeIdealOf ⟨x, hx⟩).symm)
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' ({x} : Set X)) = _
  rw [hpre, PrimeSpectrum.vanishingIdeal_singleton]

/-- Away from the original point the same ideal is the unit ideal. -/
theorem ideal_eq_top (U : X.affineOpens) (hx : x ∉ U.1) :
    (ideal X x hclosed).ideal U = ⊤ := by
  have hpre : U.2.fromSpec.base ⁻¹' ({x} : Set X) = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    change U.2.fromSpec.base p = x at hp
    exact hx (hp ▸ (U.2.isoSpec.inv.base p).2)
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' ({x} : Set X)) = _
  rw [hpre, PrimeSpectrum.vanishingIdeal_empty]

/-- The canonical rational point section has precisely this original ideal. -/
theorem closedPointSection_ker {k : Type u} [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    (closedPointSection f x hclosed).ker = ideal X x hclosed := by
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  letI : IsClosedImmersion (closedPointSection f x hclosed) := by
    unfold closedPointSection
    infer_instance
  have hrange : Set.range (closedPointSection f x hclosed).base = {x} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact closedPointSection_base f x hclosed t
    · intro hy
      have hyx : y = x := hy
      subst y
      exact ⟨Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))),
        closedPointSection_base f x hclosed _⟩
  have hs : (closedPointSection f x hclosed).ker.support = ⟨{x}, hclosed⟩ := by
    apply SetLike.coe_injective
    change ((closedPointSection f x hclosed).ker.support : Set X) = {x}
    rw [Scheme.Hom.support_ker, hrange, hclosed.closure_eq]
  calc
    (closedPointSection f x hclosed).ker =
        (closedPointSection f x hclosed).ker.radical :=
      (SchematicImageDenseOpen.ker_radical _).symm
    _ = Scheme.IdealSheafData.vanishingIdeal
        (closedPointSection f x hclosed).ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = ideal X x hclosed := by rw [hs]; rfl

#print axioms ideal_eq_prime
#print axioms ideal_eq_top
#print axioms closedPointSection_ker

end KltDP.Geometry.ClosedPointVanishingIdeal
