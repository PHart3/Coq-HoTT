From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup AbHom Biproduct.
Require Import Pointed.Core pPushout pSusp pCofiber.
Require Import Homotopy.Homology.

Local Open Scope pointed_scope.

(** * The Mayer-Vietoris sequence for homology *)

Generalizable Variables Z.

Section MVHom.

  Context `{Integers Z} (Hom : HomologyTheory) {C A B : pType} {n : Z}.

  Definition MV_boundary_map : forall {f : C ->* A} {g : C ->* B},
      C_obj Hom (1 + n) (ppushout f g) $-> C_obj Hom n C
    := fun f g => C_susp Hom C $o fmap (C_obj Hom (1 + n)) ext_glue.

  Definition MV_push_diff : forall {f : C ->* A} {g : C ->* B},
    ab_biprod (C_obj Hom n A) (C_obj Hom n B) $-> C_obj Hom n (ppushout f g)
    := fun f g => ab_biprod_rec
         (fmap (C_obj Hom n) ptd_pushl) (inverse_hom (fmap (C_obj Hom n) ptd_pushr)).

  Definition MV_po_to_prod : forall (f : C ->* A) (g : C ->* B),
      C_obj Hom n C $-> ab_biprod (C_obj Hom n A) (C_obj Hom n B)
    := fun f g => ab_biprod_corec (fmap (C_obj Hom n) f) (fmap (C_obj Hom n) g).
  
End MVHom.
