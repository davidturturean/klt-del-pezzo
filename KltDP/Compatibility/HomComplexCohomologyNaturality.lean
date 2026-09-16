/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
import KltDP.Compatibility.HomComplexCohomology

/-!
# Naturality of the Hom-complex cocycle-quotient comparison

Port of the actual postcomposition and homology-map-data blocks of Mazur's
`SheafDerivedGlobalSections` at 9327963d4ec14fba49c7b14b004fd00707ffc2e9.
The source complex is generalized from a complex concentrated in degree
zero to an arbitrary original complex: none of these proofs uses single
support. Category names and visibility are adapted to the pinned API.
The comparison uses the actual chain map, induced cocycle quotient map,
and canonical homology map.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace KltDP.HomComplexComparison

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {F : CochainComplex C ℤ}

def homComplexPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    F.HomComplex K ⟶
      F.HomComplex L where
  f n := AddCommGrp.ofHom
    { toFun := fun z ↦ z.comp (.ofHom f) (add_zero n)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  comm' i j _ := by
    apply AddCommGrp.ext
    intro z
    exact CochainComplex.HomComplex.δ_comp_ofHom z f j

lemma homComplexPostcomp_f_apply {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      F K n) :
    ((homComplexPostcomp f).f n).hom z =
      z.comp (.ofHom f) (add_zero n) :=
  rfl

def cocyclePostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cocycle F K n →+
      CochainComplex.HomComplex.Cocycle F L n where
  toFun z := z.postcomp f
  map_zero' := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]
  map_add' x y := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]

def cohomologyClassPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass
        F K n →+
      CochainComplex.HomComplex.CohomologyClass
        F L n :=
  CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
    ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom
      F L n).comp (cocyclePostcomp f n)) (by
        rintro z ⟨m, hm, β, hβ⟩
        rw [AddMonoidHom.mem_ker]
        change CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) = 0
        rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
        refine ⟨m, hm, β.comp (.ofHom f) (add_zero m), ?_⟩
        rw [CochainComplex.HomComplex.Cocycle.postcomp_coe, ← hβ]
        exact CochainComplex.HomComplex.δ_comp_ofHom β f n)

lemma cohomologyClassPostcomp_mk {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle
      F K n) :
    cohomologyClassPostcomp f n (CochainComplex.HomComplex.CohomologyClass.mk z) =
      CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) :=
  rfl

def homComplexPostcompLeftHomologyMapData {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrp.{v} (.up ℤ) n).map
        (homComplexPostcomp f))
      (CochainComplex.HomComplex.leftHomologyData
        F K n)
      (CochainComplex.HomComplex.leftHomologyData
        F L n) where
  φK := AddCommGrp.ofHom (cocyclePostcomp f n)
  φH := AddCommGrp.ofHom (cohomologyClassPostcomp f n)
  commi := by ext; rfl
  commf' := by
    let hK := CochainComplex.HomComplex.leftHomologyData
      F K n
    let hL := CochainComplex.HomComplex.leftHomologyData
      F L n
    let φ := (HomologicalComplex.shortComplexFunctor AddCommGrp.{v} (.up ℤ) n).map
      (homComplexPostcomp (F := F) f)
    let φK : hK.K ⟶ hL.K := AddCommGrp.ofHom (cocyclePostcomp f n)
    change hK.f' ≫ φK = φ.τ₁ ≫ hL.f'
    have hcommi : φK ≫ hL.i = hK.i ≫ φ.τ₂ := by
      ext
      rfl
    apply (cancel_mono hL.i).1
    calc
      (hK.f' ≫ φK) ≫ hL.i = hK.f' ≫ hK.i ≫ φ.τ₂ := by
        rw [Category.assoc, hcommi]
      _ = ((F.HomComplex K).sc n).f ≫
          φ.τ₂ := by rw [← Category.assoc, hK.f'_i]
      _ = φ.τ₁ ≫ ((F.HomComplex L).sc n).f :=
        φ.comm₁₂.symm
      _ = (φ.τ₁ ≫ hL.f') ≫ hL.i := by rw [Category.assoc, hL.f'_i]
  commπ := by ext; rfl

lemma homologyAddEquiv_homComplexPostcomp {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : ↑((F.HomComplex K).homology n)) :
    CochainComplex.HomComplex.homologyAddEquiv
        F L n
        (((HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℤ) n).map
          (homComplexPostcomp f)).hom x) =
      cohomologyClassPostcomp f n
        (CochainComplex.HomComplex.homologyAddEquiv
          F K n x) := by
  rw [HomologicalComplex.homologyFunctor_map]
  let hK := CochainComplex.HomComplex.leftHomologyData
    F K n
  let hL := CochainComplex.HomComplex.leftHomologyData
    F L n
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrp.{v} (.up ℤ) n).map
    (homComplexPostcomp (F := F) f)
  let γ := homComplexPostcompLeftHomologyMapData (F := F) f n
  change (hL.homologyIso.hom).hom ((ShortComplex.homologyMap φ).hom x) =
    (AddCommGrp.ofHom (cohomologyClassPostcomp f n)).hom ((hK.homologyIso.hom).hom x)
  exact ConcreteCategory.congr_hom γ.homologyMap_comm x

end

end KltDP.HomComplexComparison
