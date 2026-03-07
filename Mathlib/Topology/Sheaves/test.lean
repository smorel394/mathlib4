module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Abelian TopologicalSpace TopCat Limits Sheaf Opposite

variable {X : TopCat.{u}}

namespace Sheaf

section

abbrev embed (U : Opens X) : (Opens.toTopCat X).obj U ⟶ X := Opens.inclusion' U

noncomputable abbrev restrict (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⋙ Sheaf.pushforward AddCommGrpCat
    (Opens.inclusion' U)

--local instance (U : Opens X) : PreservesFiniteLimits (restrict U) := inferInstance

noncomputable abbrev restrict_sections_top (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((restrict U).obj F).val.obj (op ⊤) ≅ F.val.obj (op U) :=
  (((sheafToPresheaf _ _).mapIso ((((Opens.isOpenEmbedding U)).sheafPullbackIso _).app F))).app
  (Opposite.op ⊤) ≪≫ U.sheafPullback_sections_top _ F

lemma restrict_section_top_hom_naturality (U : Opens X) {F F' : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ F') (s : ((restrict U).obj F).val.obj (op ⊤)) :
    (restrict_sections_top U F').hom (((restrict U).map f).val.app (op ⊤) s) =
    f.val.app (op U) ((restrict_sections_top U F).hom s) := sorry

lemma restrict_section_top_inv_naturality (U : Opens X) {F F' : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ F') (s : F.val.obj (op U)) :
    (restrict_sections_top U F').inv (f.val.app (op U) s) =
    ((restrict U).map f).val.app (op ⊤) ((restrict_sections_top U F).inv s) := sorry

local instance (U : Opens X) : (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).Additive :=
  sorry

local instance (U : Opens X) : (restrict U).Additive := sorry

noncomputable abbrev to_restrict (U : Opens X) :
    𝟭 _ ⟶ restrict U := (Sheaf.pullbackPushforwardAdjunction _ (Opens.inclusion' U)).unit

lemma restrict_sections_top_inv_eq_to_restrict (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (s : F.val.obj (op ⊤)) :
    ((to_restrict U).app F).val.app (op ⊤) s = (restrict_sections_top U F).inv
    (Presheaf.restrictOpen s U (by simp)) := sorry

local instance (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    IsFlasque ((restrict U).obj F) := by
  have := IsFlasque.pullbackIsFlasqueOfIsOpenEmbedding (Opens.isOpenEmbedding U)
  apply IsFlasque.pushforwardIsFlasque

local instance to_restrict_epi_of_flasque (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasque F] : Epi ((to_restrict U).app F) := sorry
-- This needs the stuff I did in the branch `pushpulladjunction`, to identify `to_restrict`
-- to a restriction map. The theorem is call `truc` right now.

/-
First we set up some objects that will be useful for the proof:
* A short exact sequence `S` or `pres` : 0 -> F -> I -> G -> 0 with I injective.
* A short exact sequence `restrict_pres` : `0 -> (restict U).obj F -> (restrict U).obj I -> H -> 0`.
* A monomorphism `ι : H -> (restrict U).obj G` whose composition with `restrict_pres.g` is
`(restrict U).map S.g`.
* An epimorphism `η : G ⟶ H` such that `η ≫ ι = (to_restrict U).app G` and
`S.g ≫ η = (to_restrict U).app I ≫ restrict_pres.g`.
-/

noncomputable section

variable (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

def injpres : InjectivePresentation F := Classical.choice (EnoughInjectives.presentation F)

local instance : Mono (injpres F).f := (injpres F).mono
local instance : Injective (injpres F).J := (injpres F).injective

def pres := ShortComplex.mk (injpres F).f (cokernel.π (injpres F).f) (by cat_disch)

local instance : Mono (pres F).f := by dsimp [pres]; infer_instance
local instance : Epi (pres F).g := by dsimp [pres]; infer_instance
local instance : Injective (pres F).X₂ := by dsimp [pres]; infer_instance

lemma pres_exact : (pres F).ShortExact :=
  ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)

def restrict_pres := ShortComplex.mk ((restrict U).map (injpres F).f)
  (cokernel.π ((restrict U).map (injpres F).f)) (by cat_disch)

local instance : Mono (restrict_pres U F).f := by dsimp [restrict_pres]; infer_instance
local instance : Epi (restrict_pres U F).g := by dsimp [restrict_pres]; infer_instance

lemma restrict_pres_exact : (restrict_pres U F).ShortExact :=
  ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)

lemma restrict_pres'_exact : ((pres F).map (restrict U)).Exact :=
  ((restrict U).preservesFiniteLimits_iff_forall_exact_map_and_mono.mp inferInstance _
  (pres_exact F)).1

def ι : (restrict_pres U F).X₃ ⟶ (restrict U).obj (pres F).X₃ :=
  cokernel.desc ((restrict U).map (pres F).f) ((restrict U).map (pres F).g)
  (by rw [← Functor.map_comp, (pres F).zero, Functor.map_zero])

lemma ιcond : (restrict_pres U F).g ≫ ι U F = ((pres F).map (restrict U)).g := by
  dsimp [ι, restrict_pres, pres]; cat_disch

set_option backward.isDefEq.respectTransparency false in
local instance : Mono (ι U F) := by
  refine Preadditive.mono_of_cancel_zero _ (fun u hu ↦ ?_)
  obtain ⟨A, v, _, w, hvw⟩ := surjective_up_to_refinements_of_epi (restrict_pres U F).g u
  rw [← cancel_epi v, comp_zero, hvw]
  have eq : w ≫ ((pres F).map (restrict U)).g = 0 := by
    rw [← ιcond, ← Category.assoc, ← hvw, Category.assoc, hu, comp_zero]
  obtain ⟨A', x, _, y, hxy⟩ := (restrict_pres'_exact U F).exact_up_to_refinements _ eq
  rw [← cancel_epi x, comp_zero, ← Category.assoc, hxy, Category.assoc]
  change y ≫ ((restrict_pres U F).f ≫_) = 0
  rw [ShortComplex.zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
def η : (pres F).X₃ ⟶ (restrict_pres U F).X₃ :=
  cokernel.desc (pres F).f ((to_restrict U).app (pres F).X₂ ≫ (restrict_pres U F).g)
    (by simp only [← cancel_mono (ι U F), Category.assoc, ιcond, ShortComplex.map_g]
        rw [← (to_restrict U).naturality];
        simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, ShortComplex.zero_assoc,
          zero_comp])

set_option backward.isDefEq.respectTransparency false in
lemma ηcond₁ : η U F ≫ ι U F = (to_restrict U).app (pres F).X₃ := by
  dsimp [η]
  rw [← cancel_epi (cokernel.π (pres F).f), ← Category.assoc, cokernel.π_desc, Category.assoc,
    ιcond, ShortComplex.map_g, ← (to_restrict U).naturality, Functor.id_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma ηcond₂ : (pres F).g ≫ η U F = (to_restrict U).app (pres F).X₂ ≫ (restrict_pres U F).g := by
    rw [← cancel_mono (ι U F), Category.assoc, ηcond₁, Category.assoc, ιcond, ShortComplex.map_g,
      ← (to_restrict U).naturality, Functor.id_map]

set_option backward.isDefEq.respectTransparency false in
local instance : Epi (η U F) := epi_of_epi_fac (ηcond₂ U F)

def pullback_pres := (pres F).map (Sheaf.pullback _ (Opens.inclusion' U))

lemma pullback_pres_exact : (pullback_pres U F).ShortExact :=
  (pres_exact F).map (Sheaf.pullback _ (Opens.inclusion' U))

/--
Statement (**) from the notes, i.e. the fact that `H^r(U,G) -> H^{r+1}(U,F)` is bijective
(where `G` is the third sheaf in `pres F`).
Uses the fact that pullbacks are exact.
-/
lemma bijective_H_pullback_pres (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X) (r : ℕ) :
    Function.Bijective (H.connectingHom (pullback_pres_exact U F) r (r + 1)) := sorry

lemma bijective_H_pres (F : TopCat.Sheaf AddCommGrpCat.{u} X) (r : ℕ) :
    Function.Bijective (H.connectingHom (pres_exact F) r (r + 1)) := sorry

lemma restrict_sequence_short_exact {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) (U : Opens X) {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (vanish : ∀ (V : B), Subsingleton (H ((Sheaf.pullback _ (Opens.inclusion' (U ⊓ V))).obj
    S.X₁) 1)) : (S.map (restrict U)).ShortExact := sorry

local instance : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := hasExt_of_enoughInjectives _
-- Why do I need to declare this again?

set_option backward.isDefEq.respectTransparency false in
/--
Base case of the induction in `prop1`.
-/
theorem prop1_base (F : TopCat.Sheaf AddCommGrpCat.{u} X) {B : Set (Opens X)}
    (hB : Opens.IsBasis B) (c : H F 1) :
    ∃ (I : Type u) (U : I → Opens X) (_ : IsOpenCover U),
    (∀ i, U i ∈ B ∧ TopCat.Sheaf.H.map ((to_restrict (U i)).app F) 1 c = 0) := by
  have : Injective (pres F).X₂ := by dsimp [pres]; infer_instance
-- Why does Lean find the local instance I defined earlier?
  have : Subsingleton (Ext ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u, 0} ℤ))) (pres F).X₂ 1) :=
    Abelian.Ext.subsingleton_of_injective _ _ 0
-- The first cohomology group of `(pres F).X₂` vanishes.
  obtain ⟨s, hs⟩ := Abelian.Ext.covariant_sequence_exact₁.{u} _ (pres_exact F) c
    (Subsingleton.elim _ _) (n₀ := 0) rfl
-- Using the long cohomology sequence, we find a global section `s` is `(pres F).X₃` that is
-- sent to `c` by the connecting morphism.
-- Technically `s` is not a section but an element of `H (pres F).X₃ 0`, so we need to apply
-- `TopCat.Sheaf.H.equiv₀` to make it a section.
  have : Sheaf.IsLocallySurjective (pres F).g :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mpr (pres_exact F).epi_g
  obtain ⟨I, U, hU, t, h⟩ := Presheaf.exists_lift_cover_basis_of_isLocallySurjective this hB
    (TopCat.Sheaf.H.equiv₀ (pres F).X₃ s)
-- As `(pres F).g : (pres F).X₂ ⟶ (pres F).X₃` is an epimorphism of sheaves, the section `s`
-- lifts locally to sections of `(pres F).X₂`, on a cover `U : ι → Opens X`.
  refine ⟨I, U, hU, fun i ↦ ⟨(h i).1, ?_⟩⟩
  have eq₁ : (TopCat.Sheaf.H.map ((to_restrict (U i)).app F) 1) c = (TopCat.Sheaf.H.map
      (η (U i) F) 0 s).comp (restrict_pres_exact (U i) F).extClass (zero_add _) := by
    rw [← hs]
    dsimp [TopCat.Sheaf.H.map, H.map, Ext.postcomp]
    erw [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply, AddMonoidHom.flip_apply,
        Ext.bilinearComp_apply_apply]
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
    have := (pres_exact F).extClass_naturality (restrict_pres_exact (U i) F) (ShortComplex.homMk
        ((to_restrict (U i)).app F) ((to_restrict (U i)).app (pres F).X₂)
        (η  (U i) F) (by dsimp [restrict_pres, pres]; simp) (ηcond₂ (U i) F).symm)
    rw [dsimp% this]
-- The image of `c` by the map `F.H 1 X ⟶ ((restrict (U i)).obj F).H 1 X` is equal to the image by
-- `(restrict_pres (U i) F).X₃.H 0 X ⟶ ((restrict (U i)).obj F).H 1 X` of the image of `s`
-- by `H.map (η (U i) F)`.
  rw [eq₁]
  have eq₂ : TopCat.Sheaf.H.map (η (U i) F) 0 s = TopCat.Sheaf.H.map (restrict_pres (U i) F).g 0
        ((TopCat.Sheaf.H.equiv₀ (restrict_pres (U i) F).X₂).symm
        ((restrict_sections_top (U i) (pres F).X₂).inv (t i))) := by
    have := ((restrict_sections_top (U i) (pres F).X₂).inv (t i))
    apply (TopCat.Sheaf.H.equiv₀ (restrict_pres (U i) F).X₃).injective
    have : Mono (ι (U i) F) := inferInstance
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback
        ((ι (U i) F).val.app (op ⊤))).mp inferInstance
    rw [TopCat.Sheaf.H.equiv₀_naturality, ← TopCat.Sheaf.H.map_comp_apply, ηcond₁]
    conv_rhs => rw [← TopCat.Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
    have := ιcond (U i) F
    apply_fun (fun x ↦ x.val.app (op ⊤) ((((ConcreteCategory.hom
        (restrict_sections_top (U i) (pres F).X₂).inv) (t i))))) at this
    convert this.symm
    erw [← restrict_section_top_inv_naturality]; rw [(h i).2]
    rw [← TopCat.Sheaf.H.equiv₀_naturality]
    erw [restrict_sections_top_inv_eq_to_restrict]
  rw [eq₂]
  have := (H.longSequence_exact (restrict_pres_exact (U i) F) 0 1 rfl).zero 1
  dsimp [H.longSequence, Ext.covariantSequence] at this
  exact congr($this _)

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    Subsingleton (H ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type u) (U : I → Opens X) (_ : IsOpenCover U),
    (∀ i, U i ∈ B ∧ TopCat.Sheaf.H.map ((to_restrict (U i)).app F) (n + 1) c = 0) := by
  induction n generalizing F with
  | zero => exact prop1_base F hB c
  | succ n hn =>
    have vanishG : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B → Subsingleton
        (H ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj (pres F).X₃) r) := by
      intro r U h₁ h₂ hU
      have : Subsingleton ((pullback_pres U F).X₁.H (r + 1)) := vanish (r + 1) U (by lia)
        (by lia) hU
      exact (Equiv.ofBijective _ (bijective_H_pullback_pres F U r)).subsingleton
    have he : ∀ (U : Opens X), U ∈ B → ((pres F).map (restrict U)).ShortExact :=
      fun U hU ↦ restrict_sequence_short_exact (pres_exact F) U hB
        (fun V ↦ vanish 1 (U ⊓ V) (le_refl 1) (by lia) (hinter U V.1 hU V.2))
    obtain ⟨c', hc'⟩ := (bijective_H_pres F (n + 1)).2 c
    obtain ⟨I, U, hcover, hU⟩ := hn (pres F).X₃ vanishG c'
    use I, U, hcover
    refine fun i ↦ ⟨(hU i).1, ?_⟩
    rw [← hc']
    have := H.connectingHom_naturality (pres_exact F) (he (U i) (hU i).1) ((pres F).mapNatTrans
      (to_restrict (U i))) (n + 1) (n + 1 + 1) rfl c'
    dsimp [pres, TopCat.Sheaf.H.map] at this ⊢
    rw [this]
    have := (hU i).2
    dsimp [TopCat.Sheaf.H.map, pres] at this
    rw [this]
    erw [(H.connectingHom (he (U i) (hU i).1) (n + 1) (n + 1 + 1) rfl).map_zero]

end

end

end Sheaf

end CategoryTheory

open TopologicalSpace CategoryTheory Topology Opposite

@[simps!]
def CategoryTheory.Adjunction.sheafPushforwardContinuous {C : Type*} [Category* C] {D : Type*}
    [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    [G.IsContinuous K J] (E : Type*) [Category* E] :
    F.sheafPushforwardContinuous E J K ⊣ G.sheafPushforwardContinuous E K J where
  unit.app P := { val := (adj.op.whiskerLeft _).unit.app P.val }
  counit.app P := { val := (adj.op.whiskerLeft _).counit.app P.val }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.val
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.val

variable (C : Type*) [Category* C] {X : TopCat.{u}} {Y : TopCat.{u}} {f : Y ⟶ X}
  (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

abbrev restrict : Sheaf C X ⥤ Sheaf C Y := by
  haveI := hf.functor_isContinuous
  exact hf.functor.sheafPushforwardContinuous C ..

abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f := by
  haveI := hf.functor_isContinuous
  exact Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

variable (F : Sheaf C X) (U V : Opens X)

abbrev toRestrict := (restrictPushforwardAdjunction C U.isOpenEmbedding).unit

example : ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F).val.obj (op V) =
    F.val.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))) := rfl

example : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = U ⊓ V := by aesop

lemma toRestrict_app_val_all : ((toRestrict C U).app F).val.app (op V) =
    F.val.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by simp

lemma toRestrict_app_val_app_epi [IsFlasque F] : Epi (((toRestrict C U).app F).val.app (op V)) := by
  rw [toRestrict_app_val_all]
  apply Presheaf.IsFlasque.map_epi

lemma restrict_comp_pushforward_isFlasque [IsFlasque F] :
    IsFlasque ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F) where
  epi {U V i} := by
    dsimp
    apply Presheaf.IsFlasque.map_epi

end TopCat.Sheaf
