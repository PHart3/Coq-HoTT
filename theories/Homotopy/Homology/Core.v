From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Colimits.Pushout.
Require Import Pointed.Core pCofiber pEquiv pSusp.
Require Import Homotopy.Cofiber.
Require Import Types.Paths.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** * Generalized homology theories *)

Generalizable Variables Z.

Class HomologyTheory `{Integers Z} := {
    C_obj : Z -> pType -> AbGroup;
    C_0ftor :: forall z, Is0Functor (C_obj z);
    C_1ftor :: forall z, Is1Functor (C_obj z);
    C_exactness : forall {n : Z} {X Y : pType} (f : X ->* Y),
      GrpIsExact (fmap (C_obj n) f) (fmap (C_obj n) (ptd_cofib f));
    C_susp : forall {n : Z} (X : pType),
      GroupIsomorphism (C_obj (1 + n) (psusp X)) (C_obj n X);
    C_susp_fmap : forall {n : Z} {X Y : pType} (f : X ->* Y),
      fmap (C_obj n) f ∘ C_susp X == C_susp Y ∘ fmap (C_obj (1 + n)) (fmap psusp f);
    }.

(** Homology is independent of basepoint *)

Section Basepoint_ind.
  
  Context `{Hom : HomologyTheory} {n : Z}.
  
  Definition Homol_obj_bpind {X : Type} {x y : X} : GroupIsomorphism (C_obj n [X, x]) (C_obj n [X, y]) :=
    grp_iso_compose (C_susp [X, y]) (grp_iso_inverse (C_susp [X, x])).

  Lemma C_susp_fmap_rotate {X Y : pType} {f : X ->* Y} :
    fmap (C_obj n) f == C_susp Y ∘ fmap (C_obj (1 + n)) (fmap psusp f) ∘ grp_iso_inverse (C_susp X).
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

(* Homology preserves equivalences *)
(* TO DO: redo using wildcat equivalences stuff *)
Definition Homol_pequiv_equiv
  {X Y : pType}
  `{Integers Z}
  {z : Z}
  {C : HomologyTheory}
  (f : X <~>* Y)
  : C_obj z X <~> C_obj z Y.
Proof.
  snapply equiv_adjointify.
  - exact (fmap (C_obj z) f).
  - exact (fmap (C_obj z) (pequiv_inverse f)).
  - lhs_V' tapply (fmap_comp (C_obj z)).
    rhs_V' tapply (fmap_id (C_obj z)).
    tapply (fmap2 (C_obj z)).
    apply peisretr.
  - lhs_V' tapply (fmap_comp (C_obj z)).
    rhs_V' tapply (fmap_id (C_obj z)).
    tapply (fmap2 (C_obj z)).
    apply peissect.
Defined.

Definition Homol_pequiv_GroupIsomorphism
  {X Y : pType}
  `{Integers Z}
  {z : Z}
  {C : HomologyTheory}
  (f : X <~>* Y)
  : GroupIsomorphism (C_obj z X) (C_obj z Y).
Proof.
  snapply Build_GroupIsomorphism.
  - exact (fmap (C_obj z) f).
  - apply Homol_pequiv_equiv.
Defined.
