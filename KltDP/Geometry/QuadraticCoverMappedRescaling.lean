import KltDP.Geometry.QuadraticCoverRescalingNaturality
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Actual quadratic maps with a coefficient map and a unit generator change

This combines the existing quotient coefficient map and unit rescaling. Its
composition rule allows affine-open restrictions and transition units to be
handled together without identifying unequal section-ring types by fiat.
All maps retain their action on base scalars and the actual adjoined root.
The root/scalar extensionality proof uses pinned quotient and polynomial
ring-homomorphism extensionality; no new quotient universal property is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Ring homomorphisms from the actual quadratic quotient are determined by
its base scalars and its actual generator. -/
theorem coverRingHom_ext {A : Type*} [CommRing A] {s : R}
    {f g : CoverAlgebra s →+* A}
    (hC : ∀ a, f (algebraMap R (CoverAlgebra s) a) =
      g (algebraMap R (CoverAlgebra s) a))
    (ht : f (root s) = g (root s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    exact hC a
  · exact ht

/-- Actual quotient map for a literal coefficient and unit-square equation. -/
def mappedRescaleHom (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) : CoverAlgebra s →+* CoverAlgebra t := by
  letI : Algebra R S := f.toAlgebra
  exact (((rescaleEquiv (f s) t v h).toAlgHom.restrictScalars R).comp
    (baseChangeCoeffHom (S := S) s)).toRingHom

@[simp]
theorem mappedRescaleHom_algebraMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (a : R) :
    mappedRescaleHom f s t v h (algebraMap R (CoverAlgebra s) a) =
      algebraMap S (CoverAlgebra t) (f a) := by
  letI : Algebra R S := f.toAlgebra
  change rescaleEquiv (f s) t v h
    (baseChangeCoeffHom (S := S) s (algebraMap R (CoverAlgebra s) a)) = _
  rw [baseChangeCoeffHom_algebraMap]
  change rescaleEquiv (f s) t v h
    (algebraMap S (CoverAlgebra (f s)) (f a)) = _
  exact rescaleEquiv_algebraMap (f s) t v h (f a)

@[simp]
theorem mappedRescaleHom_root (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    mappedRescaleHom f s t v h (root s) =
      algebraMap S (CoverAlgebra t) (v : S) * root t := by
  letI : Algebra R S := f.toAlgebra
  change rescaleEquiv (f s) t v h (baseChangeCoeffHom (S := S) s (root s)) = _
  rw [baseChangeCoeffHom_root]
  change rescaleEquiv (f s) t v h (root (f s)) = _
  exact rescaleEquiv_root (f s) t v h

/-- The composite unit-square equation follows from the two original equations. -/
theorem mappedRescaleCondition_comp (f : R →+* S) (g : S →+* T)
    (s : R) (t : S) (w : T) (v : Sˣ) (z : Tˣ)
    (h : f s = (v : S) ^ 2 * t) (h' : g t = (z : T) ^ 2 * w) :
    (g.comp f) s = ((Units.map g.toMonoidHom v * z : Tˣ) : T) ^ 2 * w := by
  change g (f s) = (g (v : S) * (z : T)) ^ 2 * w
  rw [h, map_mul, map_pow, h']
  ring

/-- Composition of the actual quotient maps has the derived coefficient map
and the derived product transition unit. -/
theorem mappedRescaleHom_comp (f : R →+* S) (g : S →+* T)
    (s : R) (t : S) (w : T) (v : Sˣ) (z : Tˣ)
    (h : f s = (v : S) ^ 2 * t) (h' : g t = (z : T) ^ 2 * w) :
    (mappedRescaleHom g t w z h').comp (mappedRescaleHom f s t v h) =
      mappedRescaleHom (g.comp f) s w (Units.map g.toMonoidHom v * z)
        (mappedRescaleCondition_comp f g s t w v z h h') := by
  apply coverRingHom_ext
  · intro a
    simp only [RingHom.comp_apply, mappedRescaleHom_algebraMap]
  · simp only [RingHom.comp_apply, mappedRescaleHom_root, map_mul,
      mappedRescaleHom_algebraMap, Units.val_mul, Units.coe_map, mul_assoc]
    rfl

@[simp]
theorem mappedRescaleHom_id (s : R) :
    mappedRescaleHom (RingHom.id R) s s 1 (by simp) = RingHom.id (CoverAlgebra s) := by
  apply coverRingHom_ext
  · intro a
    simp only [mappedRescaleHom_algebraMap, RingHom.id_apply]
  · simp only [mappedRescaleHom_root, Units.val_one, map_one, one_mul, RingHom.id_apply]

/-- The actual contravariant scheme map. -/
def mappedRescaleMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) : affineScheme t ⟶ affineScheme s :=
  Spec.map (CommRingCat.ofHom (mappedRescaleHom f s t v h))

/-- This map factors through the already proved affine base-change chart. -/
theorem mappedRescaleMap_eq (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    mappedRescaleMap f s t v h =
      letI : Algebra R S := f.toAlgebra
      (rescaleSpecIso (f s) t v h).hom ≫ baseChangeProjection (S := S) s := by
  letI : Algebra R S := f.toAlgebra
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

@[reassoc]
theorem mappedRescaleMap_toBase (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    mappedRescaleMap f s t v h ≫ toBase s =
      toBase t ≫ Spec.map (CommRingCat.ofHom f) := by
  letI : Algebra R S := f.toAlgebra
  rw [mappedRescaleMap_eq, Category.assoc, baseChangeProjection_toBase,
    ← Category.assoc]
  change ((rescaleSpecIso (f s) t v h).hom ≫ toBase (f s)) ≫
    Spec.map (CommRingCat.ofHom f) = _
  rw [rescaleSpecIso_hom_toBase]

/-- A base open immersion gives an actual open immersion of these quadratic charts. -/
theorem mappedRescaleMap_isOpenImmersion (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (mappedRescaleMap f s t v h) := by
  letI : Algebra R S := f.toAlgebra
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom f)))
  letI := baseChangeProjection_isOpenImmersion (S := S) s
  rw [mappedRescaleMap_eq]
  infer_instance

/-- The image is exactly the inverse image of the base-chart image. -/
theorem range_mappedRescaleMap (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    Set.range (mappedRescaleMap f s t v h).base =
      (toBase s).base ⁻¹' Set.range (Spec.map (CommRingCat.ofHom f)).base := by
  letI : Algebra R S := f.toAlgebra
  have range_iso {A B C : Scheme.{u}} (e : A ≅ B) (g : B ⟶ C) :
      Set.range (e.hom ≫ g).base = Set.range g.base := by
    rw [Scheme.comp_base, TopCat.coe_comp]
    exact Function.Surjective.range_comp (f := e.hom.base)
      (ConcreteCategory.bijective_of_isIso (C := TopCat) e.hom.base).surjective g.base
  calc
    Set.range (mappedRescaleMap f s t v h).base =
        Set.range ((rescaleSpecIso (f s) t v h).hom ≫
          baseChangeProjection (S := S) s).base :=
      congrArg (fun q : affineScheme t ⟶ affineScheme s => Set.range q.base)
        (mappedRescaleMap_eq f s t v h)
    _ = Set.range (baseChangeProjection (S := S) s).base :=
      range_iso (rescaleSpecIso (f s) t v h) (baseChangeProjection (S := S) s)
    _ = Set.range ((baseChangeSpecIso S s).inv ≫
        pullback.fst (toBase s) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).base :=
      congrArg (fun q : affineScheme (algebraMap R S s) ⟶ affineScheme s =>
        Set.range q.base) (baseChangeSpecIso_inv_fst (S := S) s).symm
    _ = Set.range
        (pullback.fst (toBase s) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).base :=
      range_iso (baseChangeSpecIso S s).symm _
    _ = (toBase s).base ⁻¹' Set.range (Spec.map (CommRingCat.ofHom f)).base :=
      Scheme.Pullback.range_fst _ _

@[reassoc]
theorem mappedRescaleMap_comp (f : R →+* S) (g : S →+* T)
    (s : R) (t : S) (w : T) (v : Sˣ) (z : Tˣ)
    (h : f s = (v : S) ^ 2 * t) (h' : g t = (z : T) ^ 2 * w) :
    mappedRescaleMap g t w z h' ≫ mappedRescaleMap f s t v h =
      mappedRescaleMap (g.comp f) s w (Units.map g.toMonoidHom v * z)
        (mappedRescaleCondition_comp f g s t w v z h h') := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (mappedRescaleHom_comp f g s t w v z h h')

@[simp]
theorem mappedRescaleMap_id (s : R) :
    mappedRescaleMap (RingHom.id R) s s 1 (by simp) = 𝟙 (affineScheme s) := by
  rw [mappedRescaleMap, mappedRescaleHom_id]
  change Spec.map (𝟙 (CommRingCat.of (CoverAlgebra s))) = 𝟙 _
  exact Spec.map_id _

end KltDP.Geometry.QuadraticCover
