From HoTT Require Import Basics.
Require Import Pointed.Core pSusp pPushout.
Require Import Homotopy.Cofiber Wedge Suspension.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.Core.

Local Open Scope pointed_scope.

(** * Pointed cofibers *)

Definition pcofiber {X Y : pType} (f : X ->* Y) : pType
  := [Cofiber f, cf_apex f].

Definition ptd_cofib {X Y : pType} (f : X ->* Y) : Y ->* pcofiber f
    := Build_pMap (cofib f) ((ap (cofib f) (point_eq f))^ @ cfglue f pt).

(** Iterated pointed cofibers *)

(* We construct the iterated cofiber map (packaged with its domain and codomain). *)
Definition iterated_ptd_cofib {X Y : pType} (f : X ->* Y) (n : nat) :
  { ST : pType * pType & (fst ST) ->* (snd ST) }.
Proof.
  napply (nat_iter n _ _).
  + exists (X, Y). exact f.
  + intros [[S T] h]. exists (T, pcofiber h). exact (ptd_cofib h).
Defined.

(* some useful cases of iterated_ptd_cofib *)

Definition ptd_cofib_2 {X Y : pType} (f : X ->* Y) : (pcofiber f) ->* (pcofiber (ptd_cofib f))
  := (iterated_ptd_cofib f 2).2.

Definition ptd_cofib_3 {X Y : pType} (f : X ->* Y) :
  (pcofiber (ptd_cofib f)) ->* (pcofiber (ptd_cofib (ptd_cofib f)))
  := (iterated_ptd_cofib f 3).2.

(** We have a pointed equivalence between the cofiber of X \/ Y -> X ⊔_Z Y and Susp Z. *)

Section CofSuspEquiv.

  (** Path algebra helper lemma *)
  Definition ap_compose_inv_concat_compose_inv2 {A B C D : Type}
    (f : B -> C) (g : A -> B) (h : D -> B)
    {x y : A} {u v : D} (p : x = y) (q : _ = _) (r : u = v) :
      ap f ((ap g p^ @ q) @ ap h (r^)^) = ap (f o g) p^ @ ap f q @ ap (f o h) r.
  Proof.
    destruct p; destruct r. cbn.
    apply (concat_l (ap_pp f (1 @ q) 1)).
    refine (whiskerR _ 1).
    exact (ap_pp f 1 q).
  Defined.

  Context {X Y Z : pType} (f : Z ->* X) (g : Z ->* Y).

  Definition cof_susp_equiv : pcofiber (Y := ppushout f g) reglue ->* psusp Z.
  Proof.
    snapply Build_pMap.
    - snapply (cofiber_rec reglue).
      + exact ext_glue.
      + exists North.
        snapply wedge_ind_FFl. 
        * intro. reflexivity.
        * intro. exact (merid (X := pointed_type Z) (point Z))^.
        * cbn.
          rhs napply (whiskerR (ap (ap _) (functor_pushout_beta_pglue _)) (merid pt)^).
          rhs napply (whiskerR
                        (ap_compose_inv_concat_compose_inv2 _ pushl pushr
                           (point_eq f) (pglue pt) (point_eq g)) (merid pt)^).
          rhs napply (whiskerR
                        (ap (fun p => _ @ p @ _) (functor_pushout_beta_pglue pt))
                        (merid pt)^).
          rhs napply (whiskerR
                        (ap011 (fun p q => (p @ ((1 @ merid pt) @ 1)) @ q)
                           (ap_V _ (point_eq f) @ ap _ (ap_const (point_eq f) North))
                           (ap_const (point_eq g) South))
                        (merid pt)^).
          assert (units_lemma : forall A {x y : A} {p : x = y},
                     1 = ((1^ @ ((1 @ p) @ 1)) @ 1) @ p^) by (destruct p; reflexivity).
          exact (units_lemma _ _ _ (merid pt)).
    - reflexivity.
  Defined.

  Definition cof_susp_equiv_rev : psusp Z ->* pcofiber (Y := ppushout f g) reglue.
  Proof.
    snapply Build_pMap.
    - refine (Susp_rec pt pt _). intro z. exact
        ((cfglue reglue (wedge_inl (f z)))^ @
         ap (cofib reglue) (pglue z) @
         cfglue reglue (wedge_inr (g z))).
    - simpl. reflexivity.
  Defined.
      
End CofSuspEquiv.
