From HoTT Require Import Basics Types WildCat.Core.
Require Import Groups.Group ExactSeq.
Require Import SuccessorStructure.

Local Open Scope succ_scope.

(** Long sequence of groups *)
Record GrpLS (N : SuccStr) : Type := {
    ls_carrier : N -> Group;
    ls_fn : forall n, (ls_carrier n.+1) $-> (ls_carrier n);
}.

Coercion ls_carrier : GrpLS >-> Funclass.
Arguments ls_carrier {N} A n : rename.
Arguments ls_fn {N} A n : rename.

(** Long exact sequence of groups *)
Record GrpLES {N : SuccStr} (A : GrpLS N) : Type := {
    ls_isexact : forall n, GrpIsExact (ls_fn A n.+1) (ls_fn A n);
}.

(** Morphism of long sequences *)
Record LSMorphism {N : SuccStr} (A B : GrpLS N) : Type := {
    grp_hom : forall n, GroupHomomorphism (A n) (B n);
    sq_commute : forall n, (grp_hom n) $o (ls_fn A n) = (ls_fn B n) $o (grp_hom n.+1);
}.

(** Isomorphism of long sequences *)
Record LSIsomorphism {N : SuccStr} {A B : GrpLS N} (ls_morphism : LSMorphism A B) : Type := {
    ls_iso_mor :> LSMorphism;
    isequiv_hom : forall n, IsEquiv (grp_hom ls_iso_mor n);
}.


(** Isomorphism of long sequences preserves exactness *)
Lemma ls_iso_preserves_exact
  {N : SuccStr}
  {A B : GrpLongSequence N}
  {A_exact : GrpLES A}
  (ls_iso : LSIsomorphism A B)
  : GrpLES B.
Proof.
  split.
  intros n.
  destruct A_exact as [H_A_exact].
  

  destruct ls_iso as [H_grp_iso H_sq_commute].
  set (phi_n := H_grp_iso n).

  (* forall n, GrpIsExact (ls_fn B n.+1) (ls_fn B n). *)
Qed.
