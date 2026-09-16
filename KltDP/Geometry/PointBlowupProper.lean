import KltDP.Geometry.AffineBlowupProper
import KltDP.Geometry.PointBlowupLocalUniqueness

/-!
# Properness of the actual glued point blowup

The inverse image of the selected affine neighborhood is the actual affine
Rees blowup. The inverse image of the closed point's complement is already
proved isomorphic to that complement, with the restricted projection as
the isomorphism. These two target opens cover the original scheme.
Pinned target-locality of `IsProper` therefore proves properness of the
actual glued projection whenever the center ideal is finitely generated.

The input contains the actual affine open immersion, its actual maximal
point, closedness of that point in the ambient scheme, and finite
generation of its ideal. Properness, projectivity, smoothness and
intersection formulas are not fields of the construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- The chosen affine chart is the actual open subscheme given by its image. -/
def affineBaseIso : Spec (CommRingCat.of R) ≅ j.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
    rw [Scheme.Opens.range_ι]
    rfl)

@[simp] theorem affineBaseIso_hom_ι :
    (affineBaseIso j).hom ≫ j.opensRange.ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The two actual chart identifications intertwine the restricted global
projection with the original affine Rees projection. -/
theorem affineNeighborhoodIso_hom_restrict :
    (affineNeighborhoodIso j q hclosed).hom ≫
        ((projection j q hclosed) ∣_ j.opensRange) =
      AffineBlowup.toSpec q.asIdeal ≫ (affineBaseIso j).hom := by
  apply (cancel_mono j.opensRange.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    affineNeighborhoodIso_hom_ι, affineBlowupι_projection,
    Category.assoc, affineBaseIso_hom_ι]

/-- Properness over the selected affine target neighborhood is transferred
through the actual source and target isomorphisms. -/
theorem projection_restrict_affine_isProper (hfg : q.asIdeal.FG) :
    IsProper ((projection j q hclosed) ∣_ j.opensRange) := by
  letI : IsProper (AffineBlowup.toSpec q.asIdeal) :=
    AffineBlowup.toSpec_isProper_of_fg q.asIdeal hfg
  have he : (projection j q hclosed) ∣_ j.opensRange =
      (affineNeighborhoodIso j q hclosed).inv ≫
        AffineBlowup.toSpec q.asIdeal ≫ (affineBaseIso j).hom := by
    rw [← affineNeighborhoodIso_hom_restrict, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- Off the selected closed point, properness follows from the previously
proved actual isomorphism whose hom is the restricted projection. -/
theorem projection_restrict_puncture_isProper :
    IsProper ((projection j q hclosed) ∣_ puncture j q hclosed) := by
  rw [← punctureIso_hom]
  infer_instance

/-- The two actual opens of the original target used for properness descent. -/
def propernessTargetOpen (i : Bool) : X.Opens :=
  if i then puncture j q hclosed else j.opensRange

omit [q.asIdeal.IsMaximal] in
/-- The affine neighborhood contains the selected point; its complement
therefore completes it to a cover of the original target. -/
theorem iSup_propernessTargetOpen :
    (⨆ i, propernessTargetOpen j q hclosed i) = ⊤ := by
  apply top_unique
  intro x _
  apply Opens.mem_iSup.mpr
  by_cases hx : x = j.base q
  · refine ⟨false, ?_⟩
    change x ∈ Set.range j.base
    exact ⟨q, hx.symm⟩
  · exact ⟨true, hx⟩

/-- Finite generation of the actual maximal center ideal implies
properness of the actual glued point-blowup projection. -/
theorem projection_isProper_of_fg (hfg : q.asIdeal.FG) :
    IsProper (projection j q hclosed) := by
  apply IsLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (propernessTargetOpen j q hclosed) (iSup_propernessTargetOpen j q hclosed)
  intro i
  cases i
  · exact projection_restrict_affine_isProper j q hclosed hfg
  · exact projection_restrict_puncture_isProper j q hclosed

/-- Over a Noetherian affine neighborhood, the actual glued point-blowup
projection is proper with no additional geometric hypothesis. -/
instance projection_isProper [IsNoetherianRing R] :
    IsProper (projection j q hclosed) :=
  projection_isProper_of_fg j q hclosed (IsNoetherian.noetherian q.asIdeal)

/-- Local Noetherianity of the original scheme supplies Noetherianity of
the actual affine chart ring and hence properness of the projection. -/
theorem projection_isProper_of_locallyNoetherian [IsLocallyNoetherian X] :
    IsProper (projection j q hclosed) := by
  letI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_of_isOpenImmersion j
  letI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩
  letI : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv Γ(Spec (CommRingCat.of R), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  infer_instance

end KltDP.Geometry.PointBlowupGluing
