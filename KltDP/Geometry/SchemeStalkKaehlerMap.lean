import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.RingTheory.Etale.Kaehler

/-!
# The original Kähler map on the original stalk rings

The scalar structures are the existing `IntrinsicNodal.baseToStalkMap` maps
of the original schemes. The given over-base triangle makes the original
stalk map an algebra map. Its canonical scalar-extended Kähler map is an
isomorphism whenever that same stalk-ring map is an isomorphism, by pinned
Mathlib's localization-at-one and formally étale differential theorems.

These are modules of differentials of the original stalk rings. Comparison
with stalks of the existing differential sheaf is a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.SchemeStalkKaehlerMap

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ X)
  (g : Y ⟶ Spec (CommRingCat.of k)) (h : q ≫ f = g) (s : Y)

include h in
/-- The original over-base triangle commutes on the original stalk rings. -/
theorem scalar_triangle :
    baseToStalkMap g s = baseToStalkMap f (q.base s) ≫ q.stalkMap s := by
  rw [← h, baseToStalkMap_comp]

/-- The native differential module of the original stalk with its original base map. -/
abbrev differentialModule {Z : Scheme.{u}}
    (p : Z ⟶ Spec (CommRingCat.of k)) (z : Z) : ModuleCat (Z.presheaf.stalk z) :=
  CommRingCat.KaehlerDifferential (baseToStalkMap p z)

private def originalScalarTower :
    letI := stalkAlgebra f (q.base s)
    letI := stalkAlgebra g s
    letI := (q.stalkMap s).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk (q.base s)) (Y.presheaf.stalk s) := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  letI := (q.stalkMap s).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun a : CommRingCat.of k ⟶ Y.presheaf.stalk s => a.hom r)
      (scalar_triangle f q g h s)

/-- Extend along the actual stalk map and apply the canonical Kähler map. -/
def map :
    (ModuleCat.extendScalars (q.stalkMap s).hom).obj (differentialModule f (q.base s)) ⟶
      differentialModule g s := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  letI := (q.stalkMap s).hom.toAlgebra
  letI := originalScalarTower f q g h s
  exact ModuleCat.ofHom
    (KaehlerDifferential.mapBaseChange k (X.presheaf.stalk (q.base s)) (Y.presheaf.stalk s))

/-- The actual map sends each original differential to the differential of
its image under the original stalk-ring map. -/
theorem map_one_tmul_d (a : X.presheaf.stalk (q.base s)) :
    map f q g h s ((1 : Y.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (q.base s),
      (q.stalkMap s).hom] (CommRingCat.KaehlerDifferential.d
        (f := baseToStalkMap f (q.base s)) a)) =
      CommRingCat.KaehlerDifferential.d (f := baseToStalkMap g s) (q.stalkMap s a) := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  letI := (q.stalkMap s).hom.toAlgebra
  letI := originalScalarTower f q g h s
  change KaehlerDifferential.mapBaseChange k (X.presheaf.stalk (q.base s))
    (Y.presheaf.stalk s) (1 ⊗ₜ[X.presheaf.stalk (q.base s)]
      KaehlerDifferential.D k (X.presheaf.stalk (q.base s)) a) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- Invertibility of the original stalk-ring map makes this same canonical
scalar-extended differential map invertible. No geometric hypothesis is added. -/
theorem map_isIso [IsIso (q.stalkMap s)] : IsIso (map f q g h s) := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  letI := (q.stalkMap s).hom.toAlgebra
  letI := originalScalarTower f q g h s
  letI : IsLocalization.Away (1 : X.presheaf.stalk (q.base s)) (Y.presheaf.stalk s) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (q.stalkMap s))
  letI : Algebra.FormallyEtale (X.presheaf.stalk (q.base s)) (Y.presheaf.stalk s) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (1 : X.presheaf.stalk (q.base s)))
  change IsIso (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
    (X.presheaf.stalk (q.base s)) (Y.presheaf.stalk s)).toModuleIso.hom
  infer_instance

/-- The isomorphism is formed from the original differential map itself. -/
def iso [IsIso (q.stalkMap s)] :
    (ModuleCat.extendScalars (q.stalkMap s).hom).obj (differentialModule f (q.base s)) ≅
      differentialModule g s := by
  letI := map_isIso f q g h s
  exact asIso (map f q g h s)

theorem iso_hom [IsIso (q.stalkMap s)] : (iso f q g h s).hom = map f q g h s := rfl

end KltDP.Geometry.SchemeStalkKaehlerMap
