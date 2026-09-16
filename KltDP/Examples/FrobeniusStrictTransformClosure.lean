import KltDP.Examples.FrobeniusGlobalGraphCompatibility
import KltDP.Geometry.SchematicImageGlued
import KltDP.Geometry.SchematicImageDenseOpen

/-!
# Actual schematic closure of the punctured lifted graph

At a finite global stage, restrict the actual residual-curve morphism to
the parameter open `D(t)`. This removes the actual next blowup center.
Its kernel ideal sheaf defines an actual quotient-glued closed subscheme
of the entire stage. The kernel is proved equal to that of the full local
residual curve, by injectivity of restriction on the integral parameter
line; no closure identity is supplied as an assumption.

This constructs the schematic closure of the actual lifted graph on the
punctured coordinate chart. Its support, reducedness, factorization, and
projection to the original closed projective graph are proved. Comparison
with the whole inverse-image definition of a global strict transform,
including the complementary projective parameter chart, remains separate.
No divisor class or intersection formula is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformClosure

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalGraphCompatibility FrobeniusGraphClosed

variable {k : Type u} [Field k]

/-- The actual principal parameter open where the exceptional parameter
coordinate is invertible. -/
def parameterPuncture : (Spec (CommRingCat.of (Polynomial k))).Opens :=
  PrimeSpectrum.basicOpen Polynomial.X

instance parameterPuncture_nonempty : Nonempty (parameterPuncture (k := k)) := by
  refine ⟨⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (Polynomial k)), ?_⟩⟩
  change (Polynomial.X : Polynomial k) ∉ (⊥ : Ideal (Polynomial k))
  simpa only [Ideal.mem_bot] using (Polynomial.X_ne_zero (R := k))

local instance parameterPuncture_noetherianSpace :
    TopologicalSpace.NoetherianSpace (parameterPuncture (k := k)).toScheme := by
  letI : TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of (Polynomial k))) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (Polynomial k)))
  exact (parameterPuncture (k := k)).ι.isOpenEmbedding.isInducing.noetherianSpace

/-- The local residual graph restricted to its actual punctured parameter
line, as a morphism into the entire constructed stage. -/
def puncturedResidualCurve (A : PlaneChartedScheme k) (n m : ℕ) :
    (parameterPuncture (k := k)).toScheme ⟶ (A.stage n).carrier :=
  parameterPuncture.ι ≫ A.residualCurve n m

/-- Its schematic closure is defined by the actual kernel ideal sheaf. -/
def liftedGraphClosureIdeal (A : PlaneChartedScheme k) (n m : ℕ) :
    (A.stage n).carrier.IdealSheafData :=
  (puncturedResidualCurve A n m).ker

/-- The punctured graph and the full residual curve have exactly the same
actual ideal sheaf of equations in the entire stage. -/
theorem liftedGraphClosureIdeal_eq (A : PlaneChartedScheme k) (n m : ℕ) :
    liftedGraphClosureIdeal A n m = (A.residualCurve n m).ker :=
  SchematicImageDenseOpen.ker_precompose_open parameterPuncture (A.residualCurve n m)

/-- The actual closed subscheme obtained by gluing the quotient rings. -/
abbrev liftedGraphClosure (A : PlaneChartedScheme k) (n m : ℕ) : Scheme.{u} :=
  (liftedGraphClosureIdeal A n m).glueData.glued

/-- Its actual inclusion into the entire current blowup stage. -/
abbrev closureInclusion (A : PlaneChartedScheme k) (n m : ℕ) :
    liftedGraphClosure A n m ⟶ (A.stage n).carrier :=
  (liftedGraphClosureIdeal A n m).gluedTo

instance closureInclusion_isClosedImmersion (A : PlaneChartedScheme k) (n m : ℕ) :
    IsClosedImmersion (closureInclusion A n m) :=
  (liftedGraphClosureIdeal A n m).gluedTo_isClosedImmersion

/-- The inclusion's actual range is the topological closure of the
punctured graph, as a consequence of the kernel support theorem. -/
theorem range_closureInclusion (A : PlaneChartedScheme k) (n m : ℕ) :
    Set.range (closureInclusion A n m).base =
      closure (Set.range (puncturedResidualCurve A n m).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (puncturedResidualCurve A n m)

/-- The same closed set is the closure of the actual full local residual
curve; equality follows from the proved ideal-sheaf identity. -/
theorem range_closureInclusion_eq_residual (A : PlaneChartedScheme k) (n m : ℕ) :
    Set.range (closureInclusion A n m).base =
      closure (Set.range (A.residualCurve n m).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo, liftedGraphClosureIdeal_eq]
  exact Scheme.Hom.support_ker (A.residualCurve n m)

/-- Reducedness follows from the actual reduced punctured parameter line
and its radical kernel; the closed scheme is not replaced by a reduction. -/
instance liftedGraphClosure_isReduced (A : PlaneChartedScheme k) (n m : ℕ) :
    IsReduced (liftedGraphClosure A n m) :=
  SchematicImageDenseOpen.image_glued_isReduced (puncturedResidualCurve A n m)

/-- The support of the actual closure is irreducible, as the closure of
an image of the actual integral parameter line. -/
theorem liftedGraphClosure_support_isIrreducible (A : PlaneChartedScheme k) (n m : ℕ) :
    IsIrreducible ((liftedGraphClosureIdeal A n m).support : Set (A.stage n).carrier) := by
  rw [liftedGraphClosureIdeal_eq, Scheme.Hom.support_ker]
  have h := (IrreducibleSpace.isIrreducible_univ
    (Spec (CommRingCat.of (Polynomial k)))).image (A.residualCurve n m).base
      (A.residualCurve n m).continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

instance liftedGraphClosure_irreducibleSpace (A : PlaneChartedScheme k) (n m : ℕ) :
    IrreducibleSpace (liftedGraphClosure A n m) := by
  let I := liftedGraphClosureIdeal A n m
  letI : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (liftedGraphClosure_support_isIrreducible A n m)
  apply (irreducibleSpace_def (liftedGraphClosure A n m)).mpr
  have h := (IrreducibleSpace.isIrreducible_univ I.support).image
    I.gluedSupportHomeomorph.symm I.gluedSupportHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, I.gluedSupportHomeomorph.symm.surjective.range_eq] using h

/-- The resulting actual closed subscheme is integral. Its dimension and
its divisor class are separate geometric conclusions. -/
instance liftedGraphClosure_isIntegral (A : PlaneChartedScheme k) (n m : ℕ) :
    IsIntegral (liftedGraphClosure A n m) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The punctured graph factors through its actual closed schematic image. -/
def puncturedToClosure (A : PlaneChartedScheme k) (n m : ℕ) :
    (parameterPuncture (k := k)).toScheme ⟶ liftedGraphClosure A n m :=
  SchematicImageGlued.toImage (puncturedResidualCurve A n m)

@[reassoc] theorem puncturedToClosure_inclusion (A : PlaneChartedScheme k) (n m : ℕ) :
    puncturedToClosure A n m ≫ closureInclusion A n m = puncturedResidualCurve A n m :=
  SchematicImageGlued.toImage_inclusion (puncturedResidualCurve A n m)

/-- The proved equality of ideal sheaves identifies the actual two
quotient-glued schemes. -/
def closureIsoResidualImage (A : PlaneChartedScheme k) (n m : ℕ) :
    liftedGraphClosure A n m ≅ SchematicImageGlued.image (A.residualCurve n m) :=
  eqToIso (congrArg (fun I : (A.stage n).carrier.IdealSheafData => I.glueData.glued)
    (liftedGraphClosureIdeal_eq A n m))

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

@[reassoc] theorem closureIsoResidualImage_hom_inclusion (A : PlaneChartedScheme k)
    (n m : ℕ) :
    (closureIsoResidualImage A n m).hom ≫ SchematicImageGlued.inclusion (A.residualCurve n m) =
      closureInclusion A n m :=
  gluedTo_eqToHom _ _ (liftedGraphClosureIdeal_eq A n m)

/-- The full local residual curve also factors through the same actual
closed subscheme, using the proved identification of quotient gluings. -/
def residualToClosure (A : PlaneChartedScheme k) (n m : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ liftedGraphClosure A n m :=
  SchematicImageGlued.toImage (A.residualCurve n m) ≫ (closureIsoResidualImage A n m).inv

@[reassoc] theorem residualToClosure_inclusion (A : PlaneChartedScheme k) (n m : ℕ) :
    residualToClosure A n m ≫ closureInclusion A n m = A.residualCurve n m := by
  rw [residualToClosure, Category.assoc,
    ← closureIsoResidualImage_hom_inclusion A n m, Iso.inv_hom_id_assoc,
    SchematicImageGlued.toImage_inclusion]

/-- The residual morphism and its selected open chart form the actual
pullback square; this is derived from the chart's open immersion. -/
theorem residualCurve_isPullback (A : PlaneChartedScheme k) (n m : ℕ) :
    IsPullback (curveInPlane (k := k) m) (𝟙 (Spec (CommRingCat.of (Polynomial k))))
      (A.stage n).chart (A.residualCurve n m) := by
  have hRange : Set.range (A.residualCurve n m).base ⊆ Set.range (A.stage n).chart.base := by
    rintro _ ⟨q, rfl⟩
    exact ⟨(curveInPlane m).base q, rfl⟩
  have hLift : IsOpenImmersion.lift (A.stage n).chart (A.residualCurve n m) hRange =
      curveInPlane m :=
    (IsOpenImmersion.lift_uniq (A.stage n).chart (A.residualCurve n m) hRange
      (curveInPlane m) rfl).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (A.residualCurve n m) (A.stage n).chart hRange

/-- On every affine open of the actual selected plane chart, the closure
ideal is the residual curve's actual kernel, with the canonical section
isomorphism explicitly retained. -/
theorem liftedGraphClosureIdeal_chart (A : PlaneChartedScheme k) (n m : ℕ)
    (U : (plane k).affineOpens) :
    (curveInPlane m).ker.ideal U =
      ((liftedGraphClosureIdeal A n m).ideal
        ⟨(A.stage n).chart ''ᵁ U, U.2.image_of_isOpenImmersion _⟩).comap
          ((A.stage n).chart.appIso U).inv.hom := by
  rw [liftedGraphClosureIdeal_eq]
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (A.residualCurve n m) (curveInPlane m) (𝟙 _) (A.stage n).chart
    (residualCurve_isPullback A n m) U

/-- In actual polynomial coordinates this kernel is precisely the
principal residual ideal `(v-u^m)`, obtained from the actual section map. -/
theorem curveInPlane_coordinateKernel (m : ℕ) :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
      (curveInPlane (k := k) m).appTop).hom) =
        Ideal.span {vCoord - uCoord ^ m} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [curveInPlane, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom,
    Polynomial.ker_evalRingHom]
  simp only [uCoord, vCoord, map_pow]

/-- A nonzero parameter cannot map to the actual origin of the plane:
the first coordinate of the monomial graph is the parameter itself. -/
theorem curveInPlane_ne_origin (m : ℕ) (q : parameterPuncture (k := k)) :
    (curveInPlane m).base q.1 ≠ originPoint := by
  intro h
  have hu : uCoord (k := k) ∈ ((curveInPlane m).base q.1).asIdeal := by
    rw [h]
    exact centerU.property
  change (Polynomial.evalRingHom (Polynomial.X ^ m : Polynomial k))
    (Polynomial.C Polynomial.X) ∈ q.1.asIdeal at hu
  exact q.2 (by simpa using hu)

/-- The actual punctured lifted graph avoids the next global blowup center. -/
theorem puncturedResidualCurve_ne_center (A : PlaneChartedScheme k) (n m : ℕ)
    (q : parameterPuncture (k := k)) :
    (puncturedResidualCurve A n m).base q ≠
      (A.stage n).chart.base (originPoint (k := k)) := by
  intro h
  apply curveInPlane_ne_origin m q
  apply (A.stage n).chart.isOpenEmbedding.injective
  exact h

/-- The actual punctured lift projects through the original closed
projective graph, with the same accumulated exponent. -/
theorem puncturedToClosure_toProjectiveGraph (n m : ℕ) :
    (puncturedToClosure (projectiveProductInitial (k := k)) n m ≫
        closureInclusion projectiveProductInitial n m) ≫ projectiveContactProjection n =
      parameterPuncture.ι ≫
        ((ProjectiveLineComparison.polynomialChartMap k 0 ≫ lineToGraph (m + n)) ≫
          graphι (m + n)) := by
  rw [puncturedToClosure_inclusion, puncturedResidualCurve, Category.assoc,
    residualCurve_factors_closedGraph]

end KltDP.Examples.FrobeniusStrictTransformClosure
