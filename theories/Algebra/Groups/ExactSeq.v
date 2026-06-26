From HoTT Require Import Basics Truncations Types WildCat.Core.
Require Import Modality.
From HoTT.Pointed Require Import Core pMap pFiber.
Require Import Groups.Group Groups.Subgroup.
Require Import Homotopy.ExactSequence.
Require Import HProp.

Local Open Scope predicate_scope.

(** * Exact sequences of groups *)

Declare Scope grpisexact_scope.
Local Open Scope grpisexact_scope.

Record GrpIsExact {A B C : Group} (i : A $-> B) (f : B $-> C) :=
  Build_GrpIsExact {
      im_sub_ker : grp_image i ⊆ grp_kernel f ;
      ker_sub_im : grp_kernel f ⊆ grp_image i ;
    }.

(* The more general definition of exactness is equivalent to the form above *)
Definition IsExact_GrpIsExact {A B C : Group} {i : A $-> B} {f : B $-> C}
  : IsExact (-1) i f -> GrpIsExact i f.
Proof.
  intro isexact.
  apply Build_GrpIsExact.
  - intros b im; cbn.
    strip_truncations; destruct im as [a p].
    lhs_V apply (ap f p).
    destruct cx_isexact.
    exact (pointed_fun a).
  - intros b ker.
    destruct isexact; cbn.
    cbn in ker.
    + rapply (Trunc_rec (n:=-1) (A:=(hfiber (cxfib cx_isexact) (b; ker)))).
      * intro x; destruct x as [x xpath].      
        apply tr.
        exists x.
        lhs_V apply (pfib_cxfib cx_isexact x).
        lhs apply (ap (pfib f) xpath).
        reflexivity.
      * exact (@center _ (conn_map_isexact (b; ker))).
Defined.

Definition GrpIsExact_IsExact {A B C : Group} {i : A $-> B} {f : B $-> C}
  : GrpIsExact i f -> IsExact (-1) i f.
Proof.
  intro grpisexact; destruct grpisexact as [im_sub_ker ker_sub_im].
  snapply Build_IsExact.
  - unfold IsComplex.
    snapply Build_pHomotopy.
    + intro a.
      exact (im_sub_ker (i _) (tr (_; 1))).
    + tapply center.
  - cbn.
    apply BuildIsSurjection.
    intro ffib; destruct ffib as [b ffibpath].
    rapply (Trunc_rec (n:=-1) (A:={x : A & i x = b})).
    + intro im; destruct im as [a apath].
      apply tr.
      exists a.
      snapply path_sigma'.
      * exact apath.
      * tapply center.
    + exact (ker_sub_im b ffibpath).
Defined.

(*
Definition Equiv_IsExact_GrpIsExact `{Funext} {A B C : Group} {i : A $-> B} {f : B $-> C}
  : (IsExact (-1) i f) <~> (GrpIsExact i f).
Proof.
  snapply equiv_equiv_iff_hprop.
  - admit. 
  - 
  - 
Defined.
 *)

Definition grpisexact_square_if {A A' B B' C C' : Group}
  {i : A $-> B} {i' : A' $-> B'}
  {f : B $-> C} {f' : B' $-> C'}
  (g : GroupIsomorphism A' A)
  (h : GroupIsomorphism B' B)
  (k : GroupIsomorphism C' C)
  (p : h $o i' $== i $o g) (q : k $o f' $== f $o h)
  {grpisexact : GrpIsExact i f}
  : GrpIsExact i' f'.
Proof.
  napply IsExact_GrpIsExact.
  refine (@isexact_square_if _ _ _ _ _ _ _ i i' f f' g h k _ _ _).
  - snapply Build_pHomotopy.
    + exact p.
    + tapply center.
  - snapply Build_pHomotopy.
    + exact q.
    + tapply center.
  - exact (GrpIsExact_IsExact grpisexact).
Defined.
