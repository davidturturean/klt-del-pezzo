import KltDP.Geometry.ClosedPointFiberSubsingleton
import KltDP.Geometry.NonclosedPointBirationalIso
import KltDP.Geometry.ProperBirationalConnectedFibers
import KltDP.Geometry.ActualResolutionExceptionalCount

/-!
# Constancy on the fibers of the original proper birational map

A nontrivial closed connected fiber is covered by original contracted
prime curves. There are only finitely many such curves. If a second proper
map contracts each of them, its image on that fiber is a finite connected
set of closed points, hence a singleton. Nonclosed target points have
singleton fibers by the original codimension-one isomorphism theorem.

Connectedness is supplied by the existing proper birational connected-fiber
theorem. No new source axiom, curve exhaustion premise or factorization is
assumed. All maps and curves are the original ones.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ContractedCurvesFiberConstancy

/-- A finite preconnected set of closed points has at most one point.
The ambient space itself need not be T1. -/
private theorem subsingleton_of_finite_closed_points
    {T : Type u} [TopologicalSpace T] {A : Set T}
    (hfinite : A.Finite) (hconnected : IsPreconnected A)
    (hclosed : ∀ x ∈ A, IsClosed ({x} : Set T)) : A.Subsingleton := by
  classical
  intro x hx y hy
  by_contra hxy
  have hrest : IsClosed (A \ {x}) := by
    rw [← Set.biUnion_of_singleton (A \ {x})]
    exact (hfinite.subset (Set.diff_subset : A \ {x} ⊆ A)).isClosed_biUnion
      (fun z hz => hclosed z hz.1)
  have hcover : A ⊆ {x} ∪ (A \ {x}) := by
    intro z hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr ⟨hz, hzx⟩
  obtain ⟨z, _, hzx, hzne⟩ := (isPreconnected_closed_iff.mp hconnected)
    {x} (A \ {x}) (hclosed x hx) hrest hcover
    ⟨x, hx, rfl⟩ ⟨y, hy, hy, Ne.symm hxy⟩
  exact hzne.2 hzx

/-- Contracting every prime contracted by the original proper birational
map makes the second proper map constant on its original point fibers. -/
theorem factorsThrough_of_proper_contracts
    {k : Type u} [Field k] {S X Y : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (f : S.toScheme ⟶ Y.toScheme)
    [IsProper π] [IsProper f] (hbir : IsBirationalScheme π)
    (hcontracts : ∀ C : S.PrimeCurve,
      IsExceptionalCurve π C → IsExceptionalCurve f C) :
    Function.FactorsThrough f.base π.base := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  have hconnected : ∀ x : X.toScheme, IsConnected (π.base ⁻¹' {x}) :=
    ProperBirationalConnectedFibers.pointFibers_connected π hbir X.normal
  letI : Surjective π := ⟨fun x => (hconnected x).nonempty⟩
  letI : Nontrivial X.toScheme := by
    rcases subsingleton_or_nontrivial X.toScheme with hsub | hnt
    · letI : Subsingleton X.toScheme := hsub
      have hd := topologicalKrullDim_nonpos_of_subsingleton X.toScheme
      rw [X.dimension_two] at hd
      exact ((WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 2)).not_le hd).elim
    · exact hnt
  let T : Set Y.toScheme :=
    ⋃ C : S.PrimeCurve, ⋃ (_ : IsExceptionalCurve π C), f.base '' (C : Set S.toScheme)
  have hTfinite : T.Finite := by
    exact (exceptionalCurves_finite_of_proper_birational π hbir).biUnion
      (fun C hC => by
        obtain ⟨y, hy⟩ := hcontracts C hC
        rw [hy]
        exact Set.finite_singleton y)
  have hTclosed : ∀ y ∈ T, IsClosed ({y} : Set Y.toScheme) := by
    intro y hy
    obtain ⟨C, hyC⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hC, hyC⟩ := Set.mem_iUnion.mp hyC
    obtain ⟨z, hz⟩ := hcontracts C hC
    have hyz : y = z := by simpa only [hz, Set.mem_singleton_iff] using hyC
    rw [hyz, ← hz]
    exact f.isClosedMap _ C.isClosed
  intro s t hst
  by_cases hclosed : IsClosed ({π.base s} : Set X.toScheme)
  · by_cases hnt : (π.base ⁻¹' {π.base s}).Nontrivial
    · have hsub : f.base '' (π.base ⁻¹' {π.base s}) ⊆ T := by
        rintro y ⟨w, hw, rfl⟩
        obtain ⟨C, hwC, hC⟩ :=
          ClosedPointFiberSubsingleton.exists_primeCurve_of_nontrivial
            S π (π.base s) hclosed (hconnected _) hnt w hw
        have hCπ : IsExceptionalCurve π C := by
          refine ⟨π.base s, Set.Subset.antisymm ?_ ?_⟩
          · rintro z ⟨v, hv, rfl⟩
            exact hC v hv
          · intro z hz
            exact ⟨w, hwC, hw.trans hz.symm⟩
        exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr
          ⟨hCπ, Set.mem_image_of_mem f.base hwC⟩⟩
      have himage := subsingleton_of_finite_closed_points
        (hTfinite.subset hsub)
        ((hconnected _).isPreconnected.image f.base f.base.hom.continuous.continuousOn)
        (fun y hy => hTclosed y (hsub hy))
      exact himage ⟨s, rfl, rfl⟩ ⟨t, hst.symm, rfl⟩
    · exact congrArg f.base ((Set.not_nontrivial_iff.mp hnt) rfl hst.symm)
  · obtain ⟨U, hsU, hU⟩ :=
      NonclosedPointBirationalIso.exists_isomorphism_open X π hbir (π.base s) hclosed
    letI : IsIso (π ∣_ U) := hU
    exact congrArg f.base
      (NonclosedPointBirationalIso.pointFiber_subsingleton_of_isIso_restrict
        π U (π.base s) hsU rfl hst.symm)

/-- For original maps over the original algebraically closed field,
properness of the second map follows from the projective surface structure. -/
theorem factorsThrough_of_contracts
    {k : Type u} [Field k] [IsAlgClosed k] {S X Y : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (f : S.toScheme ⟶ Y.toScheme)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hf : f ≫ Y.structureMorphism = S.structureMorphism)
    (hcontracts : ∀ C : S.PrimeCurve,
      IsExceptionalCurve π C → IsExceptionalCurve f C) :
    Function.FactorsThrough f.base π.base := by
  letI : IsProper f := isProper_of_comp_structureMorphism f hf
  exact factorsThrough_of_proper_contracts π f hbir hcontracts

end KltDP.Geometry.ContractedCurvesFiberConstancy

#check @KltDP.Geometry.ContractedCurvesFiberConstancy.factorsThrough_of_contracts
#print axioms KltDP.Geometry.ContractedCurvesFiberConstancy.factorsThrough_of_contracts
