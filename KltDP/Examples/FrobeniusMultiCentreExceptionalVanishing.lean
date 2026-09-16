import KltDP.Examples.FrobeniusMultiCentreExceptionalCartier
import KltDP.Examples.FrobeniusMultiCentreCrossClusterRestrictions
import KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses
import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# Actual exceptional Cartier factors vanish on the other cluster opens

The accepted support theorem puts every exceptional component over its
original selected centre. The accepted other-centre and common-complement
opens therefore miss its actual range. On those opens the original
restricted immersion has the unit kernel, and the actual exceptional
Cartier divisor restricts to the zero section of the Cartier divisor sheaf.

These are embedded kernel and Cartier-section statements. No Picard-class
replacement or new vanishing premise is used in the multi-centre results.
The section argument uses an affine cover of the actual open and also
works for an empty open, without a new integrality or generic-point
preservation premise on that open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalVanishing

open KltDP.Geometry
open FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreCurveKernels FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreCrossClusterRestrictions FrobeniusMultiCentreIsoOpenClasses
  FrobeniusMultiCentreExceptionalCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original morphism restricted to an open missing its range has
the unit kernel ideal data. -/
theorem kernel_restrict_eq_top_of_disjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hdisj : Disjoint (Set.range U.ι.base) (Set.range f.base)) :
    (f ∣_ U).ker = ⊤ := by
  letI : IsEmpty (f ⁻¹ᵁ U).toScheme :=
    ⟨fun x => Set.disjoint_left.mp hdisj
      (show f.base x.1 ∈ Set.range U.ι.base from ⟨⟨_, x.2⟩, rfl⟩) ⟨x.1, rfl⟩⟩
  exact Scheme.ker_eq_top_of_isEmpty (f ∣_ U)

/-- The Cartier divisor of an original regular kernel restricts to zero
on any open missing the morphism's actual range. -/
theorem cartierOfKernel_restrict_eq_zero_of_disjoint {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [QuasiCompact f] (hI : IdealLocallyPrincipalRegular f.ker)
    (U : Y.Opens) (hdisj : Disjoint (Set.range U.ι.base) (Set.range f.base)) :
    (cartierDivisorSheaf Y).val.map (homOfLE (le_top : U ≤ ⊤)).op
      (cartierDivisorOfIdeal Y f.ker hI) = 0 := by
  have hlocal (x : U) : ∃ W : Y.affineOpens, x.1 ∈ W.1 ∧ W.1 ≤ U := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      (isBasis_affine_open Y).exists_subset_of_mem_open x.2 U.2
    exact ⟨⟨V, hV⟩, hxV, hVU⟩
  choose W hxW hWU using hlocal
  refine (cartierDivisorSheaf Y).eq_of_locally_eq' (fun x : U => (W x).1) U
    (fun x => homOfLE (hWU x)) ?_ _ 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  · intro x
    letI : Nonempty (W x).1 := ⟨⟨x.1, hxW x⟩⟩
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact cartierDivisorOfIdeal_restrict_top Y f.ker hI (W x)
      (ker_ideal_eq_top_of_disjoint f (W x) (fun z hz =>
        Set.disjoint_left.mp hdisj
          (show f.base z ∈ Set.range U.ι.base from ⟨⟨_, hWU x hz⟩, rfl⟩) ⟨z, rfl⟩))

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- On another accepted cluster open, the original exceptional
immersion has the unit restricted kernel. -/
theorem foreignExceptional_kernel_restrict_cluster (i i' : Fin n) (hii' : i' ≠ i)
    (idx : FinalIndex.{0} q) :
    (exceptionalCurveι q n a i' idx ∣_ isoPreimage q n a i).ker = ⊤ :=
  kernel_restrict_eq_top_of_disjoint _ _ (disjoint_cluster_exceptional q n a hii' idx)

/-- On the original common centre complement, every exceptional
immersion has the unit restricted kernel. -/
theorem exceptional_kernel_restrict_complement (i : Fin n) (idx : FinalIndex.{0} q) :
    (exceptionalCurveι q n a i idx ∣_ blowdownIsoOpen q n a).ker = ⊤ :=
  kernel_restrict_eq_top_of_disjoint _ _ (disjoint_isoOpen_exceptional q n a i idx)

variable [IsAlgClosed k] (ha : Function.Injective a)

include ha

/-- The actual global exceptional Cartier divisor of another cluster
restricts to the zero section on the accepted cluster open. -/
theorem multiExceptionalDivisor_restrict_cluster (i i' : Fin n) (hii' : i' ≠ i)
    (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (cartierDivisorSheaf (multiSurface (q + 1) n a)).val.map
      (homOfLE (le_top : isoPreimage q n a i ≤ ⊤)).op
      (multiExceptionalDivisor q n a ha i' idx) = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_eq_ofKernel]
  exact cartierOfKernel_restrict_eq_zero_of_disjoint (exceptionalCurveι q n a i' idx)
    (multiExceptionalKernel_locallyPrincipalRegular q n a ha i' idx) _
    (disjoint_cluster_exceptional q n a hii' idx)

/-- Every actual global exceptional Cartier divisor restricts to zero
on the original common centre complement. -/
theorem multiExceptionalDivisor_restrict_complement (i : Fin n) (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (cartierDivisorSheaf (multiSurface (q + 1) n a)).val.map
      (homOfLE (le_top : blowdownIsoOpen q n a ≤ ⊤)).op
      (multiExceptionalDivisor q n a ha i idx) = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_eq_ofKernel]
  exact cartierOfKernel_restrict_eq_zero_of_disjoint (exceptionalCurveι q n a i idx)
    (multiExceptionalKernel_locallyPrincipalRegular q n a ha i idx) _
    (disjoint_isoOpen_exceptional q n a i idx)

end KltDP.Examples.FrobeniusMultiCentreExceptionalVanishing
