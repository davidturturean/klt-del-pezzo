import KltDP.Geometry.PrimeCurveIntersectionDegreeSum

/-!
# Sums over the points of a finite scheme with closed points

A finite scheme all of whose points are closed has discrete underlying space, so
the singletons form a finite pairwise disjoint open cover. The disjoint-cover
decomposition then expresses `dim_k H⁰(Z, O)` as the sum over the points `z` of
`dim_k Γ(Z, {z})`, and at a point with open singleton the sections over the
singleton are the stalk (the singleton is initial among open neighbourhoods).

For the intersection subscheme `C ∩ D` this gives
`intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})` under the hypotheses that the
subscheme has finitely many points and that they are closed. Deriving those
hypotheses from `dim C = 1` and `C ⊄ Supp D`, and identifying `O_{C∩D,z}` with
`O_{C,z} ⧸ (d|_C)`, are recorded in `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (Z : Scheme.{u})

/-- The singleton open of a point of a scheme with discrete underlying space. -/
def singletonOpen [DiscreteTopology Z] (z : Z) : Z.Opens := ⟨{z}, isOpen_discrete _⟩

/-- Distinct singleton opens are disjoint. -/
theorem singletonOpen_disjoint [DiscreteTopology Z] :
    Pairwise fun z z' : Z => singletonOpen Z z ⊓ singletonOpen Z z' = ⊥ := by
  intro z z' h
  apply Opens.ext
  rw [Opens.coe_inf, Opens.coe_bot]
  exact Set.singleton_inter_eq_empty.mpr fun hz => h (Set.mem_singleton_iff.mp hz)

/-- The singleton opens cover. -/
theorem singletonOpen_iSup [DiscreteTopology Z] : (⨆ z : Z, singletonOpen Z z) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup, Opens.coe_top]
  exact Set.iUnion_of_singleton Z

/-- An open singleton is an initial open neighbourhood of its point. -/
def singletonOpenNhdsIsInitial (z : Z) (hz : IsOpen ({z} : Set Z)) :
    IsInitial (⟨⟨{z}, hz⟩, Set.mem_singleton z⟩ : OpenNhds z) :=
  IsInitial.ofUniqueHom (fun U => homOfLE (Set.singleton_subset_iff.mpr U.2))
    (fun _ _ => Subsingleton.elim _ _)

/-- At a point with open singleton, the stalk is the ring of sections over the singleton. -/
def stalkIsoSingletonSections (z : Z) (hz : IsOpen ({z} : Set Z)) :
    Z.presheaf.stalk z ≅ Γ(Z, ⟨{z}, hz⟩) :=
  colimit.isoColimitCocone
    ⟨coconeOfDiagramTerminal (terminalOpOfInitial (singletonOpenNhdsIsInitial Z z hz))
        ((OpenNhds.inclusion z).op ⋙ Z.presheaf),
      colimitOfDiagramTerminal (terminalOpOfInitial (singletonOpenNhdsIsInitial Z z hz))
        ((OpenNhds.inclusion z).op ⋙ Z.presheaf)⟩

variable {k : Type u} [Field k] (f : Z ⟶ Spec (CommRingCat.of k))

/-- For a finite scheme with closed points, `dim_k H⁰(Z, O)` is the sum over the points
of the `k`-dimensions of the sections over the singletons. -/
theorem cohomologyDimension_zero_unit_eq_sum_points [Fintype Z]
    (hcl : ∀ z : Z, IsClosed ({z} : Set Z))
    (hfin : FiniteDimensional k ((ModuleCohomology.baseFunctor f 0).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf))) :
    letI : DiscreteTopology Z := DiscreteTopology.of_finite_of_isClosed_singleton hcl
    letI : ∀ z : Z, Module k Γ(Z, singletonOpen Z z) := fun z =>
      sectionsBaseModule Z (baseFieldToGlobalSections f) (singletonOpen Z z)
    ModuleCohomology.cohomologyDimension f (_root_.SheafOfModules.unit Z.ringCatSheaf) 0 =
      ∑ z : Z, Module.finrank k Γ(Z, singletonOpen Z z) := by
  letI : DiscreteTopology Z := DiscreteTopology.of_finite_of_isClosed_singleton hcl
  letI : ∀ z : Z, Module k Γ(Z, singletonOpen Z z) := fun z =>
    sectionsBaseModule Z (baseFieldToGlobalSections f) (singletonOpen Z z)
  exact cohomologyDimension_zero_unit_eq_sum f (singletonOpen Z) (singletonOpen_iSup Z)
    (singletonOpen_disjoint Z) hfin

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The sum formula over the points of a finite intersection subscheme with closed points:
`intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})`. -/
theorem intersectionDegree_eq_sum_points [Fintype (C.intersectionScheme D hD hC)]
    (hcl : ∀ z : C.intersectionScheme D hD hC, IsClosed ({z} : Set (C.intersectionScheme D hD hC))) :
    letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
      DiscreteTopology.of_finite_of_isClosed_singleton hcl
    letI : ∀ z : C.intersectionScheme D hD hC,
        Module k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
      fun z => sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
        (singletonOpen (C.intersectionScheme D hD hC) z)
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      Module.finrank k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
  cohomologyDimension_zero_unit_eq_sum_points (C.intersectionScheme D hD hC)
    (C.intersectionToSpec D hD hC) hcl (C.intersectionDegree_finiteDimensional D hD hC)

/-- Finitely many intersection points on the surface (`Set.range (C ∩ D → X) = C ∩ Supp D` by
`range_intersectionToSurface`) give a finite intersection subscheme. -/
theorem intersectionScheme_finite
    (hfin : (Set.range (C.intersectionToSurface D hD hC).base).Finite) :
    Finite (C.intersectionScheme D hD hC) := by
  have hinj : Function.Injective (C.intersectionToSurface D hD hC).base :=
    (IsClosedImmersion.base_closed (f := C.intersectionToSurface D hD hC)).toIsEmbedding.injective
  haveI := hfin.to_subtype
  exact Finite.of_injective
    (fun z => (⟨_, Set.mem_range_self z⟩ : Set.range (C.intersectionToSurface D hD hC).base))
    (fun _ _ h => hinj (Subtype.ext_iff.mp h))

/-- Intersection points closed on the surface are closed in the intersection subscheme. -/
theorem intersectionScheme_isClosed_singleton
    (hcl : ∀ x ∈ Set.range (C.intersectionToSurface D hD hC).base,
      IsClosed ({x} : Set X.toScheme))
    (z : C.intersectionScheme D hD hC) :
    IsClosed ({z} : Set (C.intersectionScheme D hD hC)) := by
  rw [(IsClosedImmersion.base_closed
    (f := C.intersectionToSurface D hD hC)).isClosed_iff_image_isClosed, Set.image_singleton]
  exact hcl _ (Set.mem_range_self z)

/-- The sum formula with surface-level hypotheses: if `C ∩ Supp D` is finite and consists of
closed points of `X`, then `intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})`. -/
theorem intersectionDegree_eq_sum_points_of_finite
    (hfin : (Set.range (C.intersectionToSurface D hD hC).base).Finite)
    (hcl : ∀ x ∈ Set.range (C.intersectionToSurface D hD hC).base,
      IsClosed ({x} : Set X.toScheme)) :
    letI : Fintype (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite D hD hC hfin
      Fintype.ofFinite _
    letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
      DiscreteTopology.of_finite_of_isClosed_singleton
        (C.intersectionScheme_isClosed_singleton D hD hC hcl)
    letI : ∀ z : C.intersectionScheme D hD hC,
        Module k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
      fun z => sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
        (singletonOpen (C.intersectionScheme D hD hC) z)
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      Module.finrank k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) := by
  letI : Fintype (C.intersectionScheme D hD hC) :=
    haveI := C.intersectionScheme_finite D hD hC hfin
    Fintype.ofFinite _
  exact C.intersectionDegree_eq_sum_points D hD hC
    (C.intersectionScheme_isClosed_singleton D hD hC hcl)

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
