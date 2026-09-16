import KltDP.Geometry.InvertibleSheafFiniteOriginalExtension
import KltDP.Geometry.InvertibleSheafOriginalOverlapEquality

/-!
# Global extension by powers of an original invertible sheaf

On a quasi-compact and quasi-separated scheme, an original quasicoherent
module section on the nonvanishing open of an original line-sheaf section
extends to the original tensor twist after a sufficiently high power.

The affine frames, finite cover, local lifts, common overlap exponent,
and globally glued section are all constructed. The conclusion uses the
actual recursive powers and actual original multiplication maps. It has
no supplied extension, overlap compatibility, or ampleness premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame InvertibleSheafSectionAdvance
open InvertibleSectionNonvanishingOpen InvertibleSheafFiniteAffineExtension
open InvertibleSheafFiniteOriginalExtension InvertibleSheafOriginalOverlapEquality

variable {X : Scheme.{u}}

private abbrev res (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U) :=
  M.val.map (homOfLE hVU).op

private theorem res_comp (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (t : M.val.obj (op U)) :
    res M hWV (res M hVU t) = res M (hWV.trans hVU) t := by
  change (M.val.presheaf.map (homOfLE hVU).op ≫
    M.val.presheaf.map (homOfLE hWV).op) t = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_naturality {M N : X.Modules} (g : M ⟶ N)
    {U V : X.Opens} (hVU : V ≤ U) (t : M.val.obj (op U)) :
    res N hVU (g.val.app (op U) t) = g.val.app (op V) (res M hVU t) :=
  (PresheafOfModules.naturality_apply g.val (homOfLE hVU).op t).symm

variable (L : InvertibleSheaf X) (M : X.Modules) (s : L.obj.sections)

/-- The actual nontrivial-line-sheaf extension theorem on an original QCQS
scheme. Every local and global section, cover, and exponent is derived. -/
theorem exists_twisted_extension [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ (n : ℕ) (v : (M ⊗ (power L n).obj).val.obj (op ⊤)),
      (M ⊗ (power L n).obj).val.map
          (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v =
        (rightTwistMap M L s n).val.app (op (nonvanishingOpen X L s)) t := by
  classical
  obtain ⟨S, hS, N, hN⟩ := eventually_exists_original_lifts L M s hX t
  let U (a : S) := chartOpen L a.val
  let D := nonvanishingOpen X L s
  let T := M ⊗ (power L N).obj
  choose v hv using hN N le_rfl
  have hlocal (a : S) : res T (show U a ⊓ D ≤ U a from inf_le_left) (v a) =
      (rightTwistMap M L s N).val.app (op (U a ⊓ D))
        (res M (show U a ⊓ D ≤ D from inf_le_right) t) := hv a
  have hpairs (a b : S) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (rightAdvance L s M N k).val.app (op (U a ⊓ U b))
          (res T (show U a ⊓ U b ≤ U a from inf_le_left) (v a)) =
        (rightAdvance L s M N k).val.app (op (U a ⊓ U b))
          (res T (show U a ⊓ U b ≤ U b from inf_le_right) (v b)) := by
    let W := U a ⊓ U b
    have hW : IsCompact (W : Set X) :=
      hXqs _ _ (Set.subset_univ _) (U a).2
        (AffineOpenRefinement.affine X L.localTrivializations.X a.val).isCompact
        (Set.subset_univ _) (U b).2
        (AffineOpenRefinement.affine X L.localTrivializations.X b.val).isCompact
    let ta := res T (show W ≤ U a from inf_le_left) (v a)
    let tb := res T (show W ≤ U b from inf_le_right) (v b)
    have haD : W ⊓ D ≤ U a ⊓ D := inf_le_inf inf_le_left le_rfl
    have hbD : W ⊓ D ≤ U b ⊓ D := inf_le_inf inf_le_right le_rfl
    have heq : res T (show W ⊓ D ≤ W from inf_le_left) ta =
        res T (show W ⊓ D ≤ W from inf_le_left) tb := by
      calc
        _ = res T haD (res T (show U a ⊓ D ≤ U a from inf_le_left) (v a)) := by
          dsimp only [ta]
          rw [res_comp, res_comp]
        _ = (rightTwistMap M L s N).val.app (op (W ⊓ D))
            (res M (show W ⊓ D ≤ D from inf_le_right) t) := by
          rw [hlocal, res_naturality, res_comp]
        _ = res T hbD (res T (show U b ⊓ D ≤ U b from inf_le_left) (v b)) := by
          rw [hlocal, res_naturality, res_comp]
        _ = _ := by
          dsimp only [tb]
          rw [res_comp, res_comp]
    exact eventually_rightAdvance_eq_on_chart L M s a.val inf_le_left hW N ta tb heq
  choose k hk using hpairs
  let K : ℕ := Finset.univ.sup (fun q : S × S => k q.1 q.2)
  have hkK (a b : S) : k a b ≤ K :=
    Finset.le_sup (f := fun q : S × S => k q.1 q.2) (Finset.mem_univ (a, b))
  let T' := M ⊗ (power L (N + K)).obj
  let z (a : S) : T'.val.obj (op (U a)) :=
    (rightAdvance L s M N K).val.app (op (U a)) (v a)
  have hcompat (a b : S) :
      res T' (show U a ⊓ U b ≤ U a from inf_le_left) (z a) =
        res T' (show U a ⊓ U b ≤ U b from inf_le_right) (z b) := by
    dsimp only [z]
    rw [res_naturality, res_naturality]
    exact hk a b K (hkK a b)
  obtain ⟨w, hw, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj T')
    U ⊤ (fun a => homOfLE (show U a ≤ ⊤ from le_top)) hS.ge z (by
      intro a b
      exact hcompat a b)
  refine ⟨N + K, w, ?_⟩
  let UD (a : S) := U a ⊓ D
  have hcoverD : D ≤ ⨆ a : S, UD a := by
    intro x hx
    have hxU : x ∈ ⨆ a : S, U a := by
      rw [hS]
      trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxU
    exact Opens.mem_iSup.mpr ⟨a, ha, hx⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj T')
    UD D (fun a => homOfLE (show UD a ≤ D from inf_le_right)) hcoverD
  intro a
  change res T' (show UD a ≤ D from inf_le_right)
      (res T' (show D ≤ ⊤ from le_top) w) =
    res T' (show UD a ≤ D from inf_le_right)
      ((rightTwistMap M L s (N + K)).val.app (op D) t)
  have hwa : res T' (show U a ≤ ⊤ from le_top) w = z a := hw a
  calc
    _ = res T' (show UD a ≤ U a from inf_le_left)
        (res T' (show U a ≤ ⊤ from le_top) w) := by rw [res_comp, res_comp]
    _ = res T' (show UD a ≤ U a from inf_le_left) (z a) :=
      congrArg (res T' (show UD a ≤ U a from inf_le_left)) hwa
    _ = (rightAdvance L s M N K).val.app (op (UD a))
        (res T (show UD a ≤ U a from inf_le_left) (v a)) :=
      res_naturality (rightAdvance L s M N K) inf_le_left (v a)
    _ = (rightAdvance L s M N K).val.app (op (UD a))
        ((rightTwistMap M L s N).val.app (op (UD a))
          (res M (show UD a ≤ D from inf_le_right) t)) :=
      congrArg ((rightAdvance L s M N K).val.app (op (UD a))) (hlocal a)
    _ = (rightTwistMap M L s (N + K)).val.app (op (UD a))
        (res M (show UD a ≤ D from inf_le_right) t) :=
      congrArg (fun g : M ⟶ T' =>
        g.val.app (op (UD a)) (res M (show UD a ≤ D from inf_le_right) t))
        (rightTwistMap_rightAdvance L s M N K)
    _ = _ := (res_naturality (rightTwistMap M L s (N + K)) inf_le_right t).symm

/-- Every sufficiently high original tensor power admits an actual global
extension; the threshold and all sections are constructed. -/
theorem eventually_exists_twisted_extension [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : (M ⊗ (power L n).obj).val.obj (op ⊤),
        (M ⊗ (power L n).obj).val.map
            (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v =
          (rightTwistMap M L s n).val.app (op (nonvanishingOpen X L s)) t := by
  obtain ⟨N, v, hv⟩ := exists_twisted_extension L M s hX hXqs t
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(rightAdvance L s M N k).val.app (op ⊤) v, ?_⟩
  calc
    _ = (rightAdvance L s M N k).val.app (op (nonvanishingOpen X L s))
        ((M ⊗ (power L N).obj).val.map
          (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v) :=
      res_naturality (rightAdvance L s M N k) le_top v
    _ = (rightAdvance L s M N k).val.app (op (nonvanishingOpen X L s))
        ((rightTwistMap M L s N).val.app (op (nonvanishingOpen X L s)) t) :=
      congrArg ((rightAdvance L s M N k).val.app (op (nonvanishingOpen X L s))) hv
    _ = _ := congrArg (fun g : M ⟶ M ⊗ (power L (N + k)).obj =>
      g.val.app (op (nonvanishingOpen X L s)) t) (rightTwistMap_rightAdvance L s M N k)

end KltDP.Geometry.InvertibleSheafSectionExtension
