import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The existing monic-factor theorem on actual open-immersion charts

An original open immersion is isomorphic to its actual image open. Transport
the normalized local factors through that original isomorphism and apply the
existing open-cover theorem. This adds no gluing construction or cocycle input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry

private def factorTransport {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N : C} (e : F.obj M ≅ F.obj N) : G.obj M ≅ G.obj N :=
  (c.app M).symm ≪≫ P.mapIso e ≪≫ c.app N

private theorem factorTransport_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N Q : C} (e : F.obj M ≅ F.obj N) (b : N ⟶ Q) (a : M ⟶ Q)
    (he : e.hom ≫ F.map b = F.map a) :
    (factorTransport F P G c e).hom ≫ G.map b = G.map a := by
  simp only [factorTransport, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← c.hom.naturality b]
  change c.inv.app M ≫ P.map e.hom ≫ P.map (F.map b) ≫ c.hom.app Q = _
  rw [← Functor.map_comp_assoc, he]
  change c.inv.app M ≫ (F ⋙ P).map a ≫ c.hom.app Q = _
  rw [c.hom.naturality a, Iso.inv_hom_id_app_assoc]

private def rangePullbackIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    schemeModulePullback j ⋙ schemeModulePullback j.isoOpensRange.inv ≅
      schemeModulePullback j.opensRange.ι :=
  schemeModulePullbackCompIso j.isoOpensRange.inv j ≪≫
    eqToIso (congrArg schemeModulePullback j.isoOpensRange_inv_comp)

/-- Transport the same original normalized factor to its actual image open. -/
def schemeModuleFactorIsoOnRange {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (e : (schemeModulePullback j).obj M ≅ (schemeModulePullback j).obj N) :
    (schemeModulePullback j.opensRange.ι).obj M ≅ (schemeModulePullback j.opensRange.ι).obj N :=
  factorTransport (schemeModulePullback j) (schemeModulePullback j.isoOpensRange.inv)
    (schemeModulePullback j.opensRange.ι) (rangePullbackIso j) e

theorem schemeModuleFactorIsoOnRange_comp {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] {M N Q : X.Modules}
    (e : (schemeModulePullback j).obj M ≅ (schemeModulePullback j).obj N)
    (b : N ⟶ Q) (a : M ⟶ Q)
    (he : e.hom ≫ (schemeModulePullback j).map b = (schemeModulePullback j).map a) :
    (schemeModuleFactorIsoOnRange j e).hom ≫ (schemeModulePullback j.opensRange.ι).map b =
      (schemeModulePullback j.opensRange.ι).map a :=
  factorTransport_comp (schemeModulePullback j) (schemeModulePullback j.isoOpensRange.inv)
    (schemeModulePullback j.opensRange.ι) (rangePullbackIso j) e b a he

variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
variable [∀ i, IsOpenImmersion (j i)]
variable (hcover : ∀ x : X, ∃ i, ∃ y : Y i, (j i).base y = x)
variable {M N Q : X.Modules} (b : N ⟶ Q) [Mono b] (a : M ⟶ Q)
variable (e : ∀ i, (schemeModulePullback (j i)).obj M ≅ (schemeModulePullback (j i)).obj N)
variable (he : ∀ i, (e i).hom ≫ (schemeModulePullback (j i)).map b =
  (schemeModulePullback (j i)).map a)

include hcover in
private theorem chartRange_cover (x : X) : ∃ i, x ∈ (j i).opensRange := by
  obtain ⟨i, y, hy⟩ := hcover x
  exact ⟨i, y, hy⟩

/-- The existing original monic factor, using the actual image-open cover. -/
def schemeModuleMonicFactorIsoOnOpenCharts : M ≅ N :=
  schemeModuleMonicFactorIsoOnOpenCover (fun i => (j i).opensRange)
    (chartRange_cover Y j hcover) b a
    (fun i => schemeModuleFactorIsoOnRange (j i) (e i))
    (fun i => schemeModuleFactorIsoOnRange_comp (j i) (e i) b a (he i))

/-- The resulting global isomorphism retains the original whole map. -/
theorem schemeModuleMonicFactorIsoOnOpenCharts_comp :
    (schemeModuleMonicFactorIsoOnOpenCharts Y j hcover b a e he).hom ≫ b = a :=
  schemeModuleMonicFactorIsoOnOpenCover_comp (fun i => (j i).opensRange)
    (chartRange_cover Y j hcover) b a
    (fun i => schemeModuleFactorIsoOnRange (j i) (e i))
    (fun i => schemeModuleFactorIsoOnRange_comp (j i) (e i) b a (he i))

end KltDP.Geometry
