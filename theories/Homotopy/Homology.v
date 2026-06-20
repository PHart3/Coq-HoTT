From HoTT Require Import Basics abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Pointed.Core pSusp pCofiber.
Require Import SuccessorStructure.

Local Open Scope succ_scope.
Local Open Scope pointed_scope.

(** * Generalized homology theories *)

Class HomologyTheory `{N : SuccStr} := {
    C_obj : N -> pType -> AbGroup;
    C_0ftor :: forall z, Is0Functor (C_obj z);
    C_1ftor :: forall z, Is1Functor (C_obj z);
    C_exactness : forall {n : N} {X Y : pType} (f : X ->* Y),
      GrpIsExact (fmap (C_obj n) f) (fmap (C_obj n) (ptd_cofib f));
    C_susp : forall {n : N} (X : pType),
      GroupIsomorphism (C_obj (n .+1) (psusp X)) (C_obj n X);
    C_susp_fmap : forall {n : N} {X Y : pType} (f : X ->* Y),
      fmap (C_obj n) f ∘ C_susp X == C_susp Y ∘ fmap (C_obj (n .+1)) (fmap psusp f);
    }.

(** Homology is independent of basepoint *)

Section Basepoint_ind.
  
  Context `{Hom : HomologyTheory} {n : N}.
  
  Definition Homol_obj_bpind {X : Type} {x y : X} : GroupIsomorphism (C_obj n [X, x]) (C_obj n [X, y]) :=
    grp_iso_compose (C_susp [X, y]) (grp_iso_inverse (C_susp [X, x])).

  Lemma C_susp_fmap_rotate {X Y : pType} {f : X ->* Y} :
    fmap (C_obj n) f == C_susp Y ∘ fmap (C_obj (n .+1)) (fmap psusp f) ∘ grp_iso_inverse (C_susp X).
  Proof.
    intro x.
    refine (_@ (C_susp_fmap f (grp_iso_inverse (C_susp X) x))). refine (ap (fmap (C_obj n) f) _).
    symmetry. apply eisretr.
  Qed.
  
  Lemma Homol_mor_bpind {X Y : pType} (f : X -> Y) {p q : f pt = pt} :
    fmap (C_obj n) (Build_pMap f p) == fmap (C_obj n) (Build_pMap f q).
  Proof.
    napply pointwise_paths_concat.
    + exact C_susp_fmap_rotate.
    + symmetry. exact C_susp_fmap_rotate.
  Qed.
  
End Basepoint_ind.
