

From HoTT Require Import Basics Types WildCat.Core Truncations.
Require Import Groups.Group Subgroup ExactSeq.
Require Import SuccessorStructure.

Local Open Scope succ_scope.

(** Long sequence of groups *)
Record LS (N : SuccStr) : Type := Build_LS {
    ls_carrier : N -> Group;
    ls_fn : forall n, (ls_carrier n.+1) $-> (ls_carrier n);
}.

Coercion ls_carrier : LS >-> Funclass.
Arguments ls_carrier {N} A n : rename.
Arguments ls_fn {N} A n : rename.

(** Exactness of a sequence S is a predicate on S *)
Record IsExactSeq {N : SuccStr} (S : LS N) := {
    is_exact_seq : forall n, GrpIsExact (ls_fn S n.+1) (ls_fn S n);
}.

(** The type of long exact sequences *)
Record LES (N : SuccStr) := Build_LES {
    les_ls : LS N;
    is_exact : IsExactSeq les_ls;
}.

Coercion les_ls : LES >-> LS.

(** Morphism of long sequences *)
Record LSMorphism {N : SuccStr} (A B : LS N) : Type := Build_LSMorphism {
    grp_hom : forall n, A n $-> B n;
    sq_commute : forall n, forall a, ((grp_hom n) $o (ls_fn A n)) a = ((ls_fn B n) $o (grp_hom n.+1)) a;
}.

(** Isomorphism of long sequences predicate *)
Record IsLSIsomorphism {N : SuccStr} {A B : LS N} (f : LSMorphism A B) : Type := {
    isequiv_ls_iso : forall n, IsEquiv (@grp_hom _ _ _ f n);
}.

(** Type of Isomorphisms of long sequences *)
Record LSIsomorphism {N : SuccStr} (A B : LS N) := Build_LSIsomorphism {
    ls_iso_morphism : LSMorphism A B;
    is_iso : forall n, IsEquiv (@grp_hom _ _ _ ls_iso_morphism n);
}.

Coercion ls_iso_morphism : LSIsomorphism >-> LSMorphism.

(** Equivalence at position n in an LSIsomorphism *)
Definition ls_equiv {N : SuccStr} {A B : LS N} (ls_iso : LSIsomorphism A B) (n : N) : A n <~> B n :=
  Build_GroupIsomorphism _ _ (grp_hom A B ls_iso n) (is_iso A B ls_iso n).

(** Isomorphism of long sequences preserves exactness *)
Lemma ls_iso_preserves_exact
  {N : SuccStr}
  {A : LES N}
  {B : LS N}
  (ls_iso : LSIsomorphism A B)
  : IsExactSeq B.
Proof.
  split.
  intros n.  
  refine ({|
    im_sub_ker := _;
    ker_sub_im := _;
  |}).
  - intros b y.
    cbn.
    strip_truncations.
    destruct y as [x p].
    set (a2 := (ls_equiv ls_iso n.+1.+1)^-1 x).
    set (a1 := (ls_equiv ls_iso n.+1)^-1 b).
    set (q := (eissect (ls_equiv ls_iso n.+1) ((ls_fn A n.+1) a2))^
                @ (ap (ls_equiv ls_iso n.+1)^-1 ((sq_commute _ _ ls_iso n.+1 a2)
                                                   @ (ap (ls_fn B n.+1) (eisretr (ls_equiv ls_iso n.+1.+1) x) @ p)))).

    set (ker_witness := im_sub_ker _ _ (is_exact_seq A (@is_exact N A) n) a1 (tr (a2; q))).
    exact (ap (ls_fn B n) (eisretr (ls_equiv ls_iso n.+1) b)^
             @ (sq_commute _ _ ls_iso n a1)^
               @ ap (ls_equiv ls_iso n) ker_witness
                 @ grp_homo_unit (ls_equiv ls_iso n)).
    
  - intros b p.
    cbn.
    cbn in p.
    set (a1 := (ls_equiv ls_iso n.+1)^-1 b).
    set (q := (eissect (ls_equiv ls_iso n) ((ls_fn A n) ((ls_equiv ls_iso n.+1)^-1 b)))^
                @ (ap (ls_equiv ls_iso n)^-1 ((sq_commute _ _ ls_iso n ((ls_equiv ls_iso n.+1)^-1 b))
                                                @ ((ap (ls_fn B n) (eisretr (ls_equiv ls_iso n.+1) b)) @ p)))
                   @ (grp_homo_unit (grp_iso_inverse (ls_equiv ls_iso n)))).
    set (im_witness := ker_sub_im _ _ (is_exact_seq A (@is_exact N A) n) ((ls_equiv ls_iso n.+1)^-1 b) q).
    cbn in im_witness.
    set (myfn := (fun (u : {x : A n.+1.+1 & ls_fn A n.+1 x = (ls_equiv ls_iso n.+1)^-1 b}) =>
            match u return (Trunc (-1) {x : B n.+1.+1 & (ls_fn B n.+1 x) = b}) with
            | (x1; path1) => tr ((ls_equiv ls_iso n.+1.+1 x1); (sq_commute _ _ ls_iso n.+1 x1)^
                                                                 @ (ap (ls_equiv ls_iso n.+1) path1) @
                                                                   (eisretr (ls_equiv ls_iso n.+1) b))
            end)).
    exact (Trunc_rec myfn im_witness).
    
Qed.
