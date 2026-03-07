module

public import Mathlib

@[expose] public section

universe u

open TopologicalSpace CategoryTheory Topology Opposite

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

@[simps!]
def Adjunction.sheafPushforwardContinuous {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
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

#check SheafOfModules.pushforwardPushforwardAdj

variable (C : Type*) [Category* C] {X : TopCat.{u}} {U : TopCat.{u}} {f : U ⟶ X}
  (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

abbrev restrict : Sheaf C X ⥤ Sheaf C U := by
  haveI := hf.functor_isContinuous
  exact hf.functor.sheafPushforwardContinuous C ..

abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f := by
  haveI := hf.functor_isContinuous
  exact Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) C

variable (F : Sheaf C X) (V : Opens X)

example : ((restrict C hf ⋙ pushforward C f).obj F).val.obj (op V) =
    F.val.obj (op (hf.functor.obj ((Opens.map f).obj V))) := rfl

abbrev toRestrict' (F : Sheaf C X) := (restrictPushforwardAdjunction C hf).unit.app F

example (F : Sheaf C X) : (F.toRestrict' C hf).val.app (op V) =
    F.val.map (hf.isOpenMap.adjunction.counit.app V).op := by
  simp

variable (U : Opens X) (V : Opens X) (F : Sheaf C X)

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

/-
namespace AlgebraicGeometry.Scheme.Modules

open TopCat Sheaf CategoryTheory AddCommGrpCat Limits

variable (n : ℕ) {X : Scheme.{u}} [IsAffine X] (F : X.Modules)

noncomputable abbrev sheaf : Sheaf Ab X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj F

/- noncomputable abbrev restrict (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⋙ Sheaf.pushforward AddCommGrpCat
    (Opens.inclusion' U) -/

#check restrict

noncomputable abbrev openRestrictPush (U : Opens X) : X.Modules ⥤ X.Modules :=
  restrictFunctor U.ι ⋙ pushforward U.ι

noncomputable abbrev toOpenRestrictPush (U : X.Opens) := (restrictAdjunction U.ι).unit

private lemma vanish_base : Subsingleton (H F.sheaf 1) := sorry


instance : Subsingleton (H F.sheaf (n + 1)) := by
  revert F X
  refine Nat.case_strong_induction_on (p := fun n => ∀ {X : Scheme} [IsAffine X] (F : X.Modules),
    Subsingleton ((F.sheaf).H (n + 1))) n vanish_base ?_
  intro n hi X _ F
  apply subsingleton_of_forall_eq 0
  intro s
  obtain ⟨I, ⟨U, ⟨_, hU⟩⟩⟩ := Sheaf.prop1 F.sheaf (n + 1) (isBasis_affineOpens X) sorry (by
    intro r U hr hrn hU
    have : r - 1 < n := sorry
    sorry) s
  have : Finite I := sorry
  let j : I → X.Modules := fun i => (openRestrictPush (U i)).obj F
  let G : X.Modules := ∏ᶜ j
  let res : F ⟶ G := Pi.lift (fun b => (toOpenRestrictPush (U b)).app F)
  haveI : Mono res := sorry
  let S := ShortComplex.mk res (cokernel.π res) (by cat_disch)
  have := hi n (Nat.le_refl n) S.X₃
  sorry


end AlgebraicGeometry.Scheme.Modules
-/
