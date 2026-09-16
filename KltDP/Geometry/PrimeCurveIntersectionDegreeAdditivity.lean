import KltDP.Geometry.PrimeCurveIntersectionFinite

/-!
# Additivity of the intersection degree over a two-piece decomposition

The intersection subscheme `C ∩ D` is finite with closed points, hence discrete: every
subset `S` of its points is open and closed, and `C ∩ D` is the disjoint union of the
open pieces `S` and `Sᶜ`. The disjoint-cover decomposition of global sections then gives
`intersectionDegree = dim_k Γ(C ∩ D, S) + dim_k Γ(C ∩ D, Sᶜ)` (base action through the
structure morphism and restriction).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable (Z : Scheme.{u}) [DiscreteTopology Z]

/-- Any set of points of a discrete scheme, as an open. -/
def discreteOpen (S : Set Z) : Z.Opens := ⟨S, isOpen_discrete S⟩

/-- The two-piece cover `{S, Sᶜ}`, indexed by `ULift Bool` (in the scheme universe). -/
def twoPieceCover (S : Set Z) : ULift.{u} Bool → Z.Opens := fun b =>
  match b.down with
  | true => discreteOpen Z S
  | false => discreteOpen Z Sᶜ

theorem twoPieceCover_iSup (S : Set Z) : (⨆ b, twoPieceCover Z S b) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup, Opens.coe_top]
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : z ∈ S
  · exact Set.mem_iUnion.mpr ⟨⟨true⟩, hz⟩
  · exact Set.mem_iUnion.mpr ⟨⟨false⟩, hz⟩

theorem twoPieceCover_disjoint (S : Set Z) :
    Pairwise fun b b' : ULift.{u} Bool => twoPieceCover Z S b ⊓ twoPieceCover Z S b' = ⊥ := by
  intro b b' hbb'
  apply Opens.ext
  rw [Opens.coe_inf, Opens.coe_bot]
  obtain ⟨b⟩ := b
  obtain ⟨b'⟩ := b'
  cases b <;> cases b'
  · exact absurd rfl hbb'
  · exact Set.compl_inter_self S
  · exact Set.inter_compl_self S
  · exact absurd rfl hbb'

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The intersection degree is additive over a decomposition of the (finite, discrete)
intersection subscheme into two disjoint closed pieces `S` and `Sᶜ`. -/
theorem intersectionDegree_eq_add_of_set (S : Set (C.intersectionScheme D hD hC)) :
    letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite' D hD hC
      DiscreteTopology.of_finite_of_isClosed_singleton
        (C.intersectionScheme_isClosed_singleton' D hD hC)
    letI : Module k Γ(C.intersectionScheme D hD hC, discreteOpen (C.intersectionScheme D hD hC) S) :=
      sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
        (discreteOpen (C.intersectionScheme D hD hC) S)
    letI : Module k Γ(C.intersectionScheme D hD hC, discreteOpen (C.intersectionScheme D hD hC) Sᶜ) :=
      sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
        (discreteOpen (C.intersectionScheme D hD hC) Sᶜ)
    C.intersectionDegree D hD hC =
      Module.finrank k Γ(C.intersectionScheme D hD hC, discreteOpen (C.intersectionScheme D hD hC) S) +
        Module.finrank k
          Γ(C.intersectionScheme D hD hC, discreteOpen (C.intersectionScheme D hD hC) Sᶜ) := by
  haveI := C.intersectionScheme_finite' D hD hC
  letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
    DiscreteTopology.of_finite_of_isClosed_singleton
      (C.intersectionScheme_isClosed_singleton' D hD hC)
  letI : ∀ b : ULift.{u} Bool, Module k Γ(C.intersectionScheme D hD hC,
      twoPieceCover (C.intersectionScheme D hD hC) S b) := fun b =>
    sectionsBaseModule (C.intersectionScheme D hD hC)
      (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
      (twoPieceCover (C.intersectionScheme D hD hC) S b)
  have h := cohomologyDimension_zero_unit_eq_sum (C.intersectionToSpec D hD hC)
    (twoPieceCover (C.intersectionScheme D hD hC) S)
    (twoPieceCover_iSup (C.intersectionScheme D hD hC) S)
    (twoPieceCover_disjoint (C.intersectionScheme D hD hC) S)
    (C.intersectionDegree_finiteDimensional D hD hC)
  have hs : (∑ b : ULift.{u} Bool, Module.finrank k
      Γ(C.intersectionScheme D hD hC, twoPieceCover (C.intersectionScheme D hD hC) S b)) =
      Module.finrank k
          Γ(C.intersectionScheme D hD hC, twoPieceCover (C.intersectionScheme D hD hC) S ⟨true⟩) +
        Module.finrank k
          Γ(C.intersectionScheme D hD hC, twoPieceCover (C.intersectionScheme D hD hC) S ⟨false⟩) := by
    rw [Fintype.sum_equiv Equiv.ulift
      (fun b : ULift.{u} Bool => Module.finrank k
        Γ(C.intersectionScheme D hD hC, twoPieceCover (C.intersectionScheme D hD hC) S b))
      (fun b : Bool => Module.finrank k
        Γ(C.intersectionScheme D hD hC, twoPieceCover (C.intersectionScheme D hD hC) S ⟨b⟩))
      (fun _ => rfl), Fintype.sum_bool]
  exact h.trans hs

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
