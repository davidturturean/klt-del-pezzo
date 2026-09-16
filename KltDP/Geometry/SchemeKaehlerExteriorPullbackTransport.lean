import KltDP.Geometry.SchemeKaehlerExteriorPullbackMap
import KltDP.Geometry.AffineDifferentialExteriorNormalization
import KltDP.Geometry.AffineModuleTildePullback

/-!
# Original exterior pullback under an equality of structure maps

Separate equality transport, the actual pullback-unit calculation and the
original affine scalar normalization before specializing to a Rees chart.
All maps are the existing differential maps and equality isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

open SchemeKaehlerSheaf AffineDifferentialExteriorNormalization

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}

theorem eqToIso_wedge_d {f g : X ⟶ Spec (CommRingCat.of k)} (h : f = g)
    (n : ℕ) (U : X.Opens) (s : Fin n → Γ(X, U)) :
    (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n) h)).hom.val.app
        (op U) (SchemeExteriorPower.wedge (baseRingSheaf f) n U
          (fun i => (baseRingDerivation f).d (s i))) =
      SchemeExteriorPower.wedge (baseRingSheaf g) n U
        (fun i => (baseRingDerivation g).d (s i)) := by
  subst g
  rfl

variable (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of k)) (h : j ≫ f = g)

/-- The original differential map followed by the actual equality transport. -/
def map (n : ℕ) :
    (schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ⟶
      SchemeExteriorPower.sheaf (baseRingSheaf g) n :=
  SchemeKaehlerExteriorPullbackMap.map f j n ≫
    (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n) h)).hom

/-- The transported map retains the original derivative-wedge normalization. -/
theorem map_unit_wedge_d (n : ℕ) (U : X.Opens) (s : Fin n → Γ(X, U)) :
    (map f j g h n).val.app (op (j ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction j).unit.app
          (SchemeExteriorPower.sheaf (baseRingSheaf f) n)).val.app (op U)
            (SchemeExteriorPower.wedge (baseRingSheaf f) n U
              (fun i => (baseRingDerivation f).d (s i)))) =
      SchemeExteriorPower.wedge (baseRingSheaf g) n (j ⁻¹ᵁ U)
        (fun i => (baseRingDerivation g).d (j.app U (s i))) := by
  subst g
  simpa only [map, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    SchemeKaehlerExteriorPullbackMap.map_unit_wedge_d f j n U s

theorem wedge_d_map_pair {T : Type*} (U : X.Opens) (s : T → Γ(X, U)) (a b : T) :
    SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
        (fun i => (baseRingDerivation f).d (s (![a, b] i))) =
      differentialWedge f U (s a) (s b) := by
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf f) 2 U)
  funext i
  fin_cases i <;> rfl

/-- Ordered pairs use the same unit map, with no rewriting inside a concrete chart. -/
theorem map_unit_pair (U : X.Opens) (s t : Γ(X, U)) :
    (map f j g h 2).val.app (op (j ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction j).unit.app
          (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)).val.app (op U)
            (differentialWedge f U s t)) =
      differentialWedge g (j ⁻¹ᵁ U) (j.app U s) (j.app U t) := by
  have hw := map_unit_wedge_d f j g h 2 U ![s, t]
  have hs := wedge_d_map_pair f U (fun r : Γ(X, U) => r) s t
  have ht := wedge_d_map_pair g (j ⁻¹ᵁ U) (fun r : Γ(X, U) => j.app U r) s t
  exact (congrArg
    (fun w => (map f j g h 2).val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)).val.app (op U) w)) hs.symm).trans
      (hw.trans ht)

section Affine

variable {A B : Type u} [CommRing A] [CommRing B]
    (fA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) (φ : A →+* B)
    (gB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k))
    (hB : Spec.map (CommRingCat.ofHom φ) ≫ fA = gB)

/-- Original affine scalar sections are normalized before chart specialization. -/
theorem map_unit_wedge_toOpen (n : ℕ) (v : Fin n → A) :
    (map fA (Spec.map (CommRingCat.ofHom φ)) gB hB n).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom φ))).unit.app
          (SchemeExteriorPower.sheaf (baseRingSheaf fA) n)).val.app (op ⊤)
            (SchemeExteriorPower.wedge (baseRingSheaf fA) n ⊤
              (fun i => (baseRingDerivation fA).d (StructureSheaf.toOpen A ⊤ (v i))))) =
      SchemeExteriorPower.wedge (baseRingSheaf gB) n ⊤
        (fun i => (baseRingDerivation gB).d (StructureSheaf.toOpen B ⊤ (φ (v i)))) := by
  refine (map_unit_wedge_d fA (Spec.map (CommRingCat.ofHom φ)) gB hB n ⊤
    (fun i => StructureSheaf.toOpen A ⊤ (v i))).trans ?_
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf gB) n ⊤)
  funext i
  exact congrArg (baseRingDerivation gB).d (AffineModuleTilde.specMap_globalScalar φ (v i))

theorem map_unit_pair_toOpen (a b : A) :
    (map fA (Spec.map (CommRingCat.ofHom φ)) gB hB 2).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom φ))).unit.app
          (SchemeExteriorPower.sheaf (baseRingSheaf fA) 2)).val.app (op ⊤)
            (differentialWedge fA ⊤ (StructureSheaf.toOpen A ⊤ a)
              (StructureSheaf.toOpen A ⊤ b))) =
      differentialWedge gB ⊤ (StructureSheaf.toOpen B ⊤ (φ a))
        (StructureSheaf.toOpen B ⊤ (φ b)) :=
  (map_unit_pair fA (Spec.map (CommRingCat.ofHom φ)) gB hB ⊤
    (StructureSheaf.toOpen A ⊤ a) (StructureSheaf.toOpen A ⊤ b)).trans
      (congrArg₂ (differentialWedge gB ⊤)
        (AffineModuleTilde.specMap_globalScalar φ a)
        (AffineModuleTilde.specMap_globalScalar φ b))

end Affine

end KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
