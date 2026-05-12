From HoTT Require Import Basics.
Require Import Types.Paths Unit.
Require Import Pointed.Core pSusp pPushout pEquiv.
Require Import Homotopy.Cofiber Wedge Suspension NullHomotopy CofibRetractInduction.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.Core.

Local Open Scope pointed_scope.

(** * Pointed cofibers *)

Definition pcofiber {X Y : Type} (f : X -> Y) : pType
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

(** The cofiber of an equivalence is equivalent to the zero object. *)

Definition unit_cofiber_equivalence {X Y : Type} {f : X -> Y} `{fe : IsEquiv X Y f}
  : pEquiv (pcofiber f) pUnit := Build_pEquiv' (@equiv_contr_unit _ contr_cofiber_equivalence) idpath.

(* some useful cases of iterated_ptd_cofib *)

Definition ptd_cofib_2 {X Y : pType} (f : X ->* Y) : (pcofiber f) ->* (pcofiber (ptd_cofib f))
  := (iterated_ptd_cofib f 2).2.

Definition ptd_cofib_3 {X Y : pType} (f : X ->* Y) :
  (pcofiber (ptd_cofib f)) ->* (pcofiber (ptd_cofib (ptd_cofib f)))
  := (iterated_ptd_cofib f 3).2.

(** We define a special variant of ext_glue (found in pPushout.v) out of
    the pointed cofiber because of a mismatch between the point of a pointed
    cofiber and that of a general pointed pushout. *)
Definition ext_glue_cof {X Y : pType} (f : X ->* Y) : pcofiber f ->* psusp X.
Proof.
  snapply Build_pMap.
  - snapply cofiber_rec.
    + exact (const South).
    + exists North.
      intro x. exact ((merid x)^).
  - reflexivity.
Defined.

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

  Definition cof_susp_equiv : pcofiber (Y := ppushout f g) (reglue f g) ->* psusp Z.
  Proof.
    snapply Build_pMap.
    - snapply (cofiber_rec (reglue f g)).
      + exact (ext_glue f g).
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

  Definition cof_susp_equiv_rev : psusp Z ->* pcofiber (Y := ppushout f g) (reglue f g).
  Proof.
    snapply Build_pMap.
    - refine (Susp_rec pt pt _). intro z. exact
        ((cfglue (reglue f g) (wedge_inl (f z)))^ @
         ap (cofib (reglue f g)) (pglue z) @
         cfglue (reglue f g) (wedge_inr (g z))).
    - simpl. reflexivity.
  Defined.
      
End CofSuspEquiv.

(** *** The pointed cofiber of reglue is the pointed suspension of the apex. *)

Section CofReglueSetup.

  Context {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}.

  Definition extreglue_nullhmtpy : NullHomotopy (ext_glue f g o reglue f g).
  Proof.
    exists North.
    snapply wedge_ind.
    - intro. reflexivity.
    - intro. exact ((merid pt)^).
    - lhs napply (transport_paths_Fl wglue idpath).
      lhs napply (concat_p1 _).
      apply (ap inverse).
      lhs napply (ap_compose (reglue f g) (ext_glue f g) wglue).
      lhs napply (ap02 (ext_glue f g) (functor_pushout_beta_pglue tt)).
      assert (ap_ap_V_concat_ap_VV :
               forall {A B C D : Type} {h : C -> D}
                      {k1 : A -> C} {k2 : B -> C} {a b : A} {x y : B}
                      (p1 : a = b) (p2 : k1 a = k2 x) (p3 : x = y),
                 ap h ((ap k1 p1^ @ p2) @ ap k2 (p3^)^)
                 = (ap (h o k1) p1)^ @ ap h p2 @ ap (h o k2) p3). {
        destruct p1. destruct p3. simpl.
        lhs napply (ap_pp h _ idpath).
        napply (whiskerR _ idpath). apply (ap_pp h idpath p2).
      }
      lhs napply (ap_ap_V_concat_ap_VV _ _ _ _ _ _ _ _ _ _ _
                    (point_eq f) (pglue pt) (point_eq g)). simpl.
      lhs napply (whiskerR
                    (ap inverse (ap_const (point_eq f) _) @@
                       functor_pushout_beta_pglue (f := f) (g := g) (B' := pUnit) pt)
                    (ap (fun x : Y => _) (point_eq g))).
      cbn. lhs napply (whiskerL _ (ap_const (point_eq g) _)).
      lhs napply (concat_p1 _ @ concat_1p _ @ concat_p1 _ @ concat_1p _).
      reflexivity.
  Defined. 
  
  Definition cofreglue_susp_map : pcofiber (reglue f g) -> psusp Z.
  Proof.
    snapply cofiber_rec.
    - exact (ext_glue f g).
    - exact extreglue_nullhmtpy.
  Defined.
  
  Definition cofreglue_susp_pmap : pcofiber (reglue f g) ->* psusp Z
    := Build_pMap cofreglue_susp_map idpath.

  Definition cofreglue_susp_map_inv : psusp Z -> pcofiber (reglue f g).
  Proof.
    snapply Susp_rec.
    - exact (cf_apex (reglue f g)).
    - exact (cf_apex (reglue f g)).
    - intro z. exact
        ((cfglue _ (wedge_inl (f z)))^
           @ ap (cofib (reglue f g)) (pglue z)
             @ cfglue _ (wedge_inr (g z))).
  Defined.

End CofReglueSetup.

Lemma cofreglue_susp_map_isequiv {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}
  : IsEquiv (cofreglue_susp_map (f := f) (g := g)).
Proof.
  (* we first strictify f and g *)
  pointed_reduce_pmap f. pointed_reduce_pmap g.
  pose (f_idp := Build_pMap f idpath : Z ->* [X, f pt]).
  pose (g_idp := Build_pMap g idpath : Z ->* [Y, g pt]).
  pose (reglue_str := reglue f_idp g_idp).
  pose (cofreglue_susp_map_str := cofreglue_susp_map (f := f_idp) (g := g_idp)).
  pose (cofreglue_susp_map_str_inv := cofreglue_susp_map_inv (f := f_idp) (g := g_idp)).
  
  snapply (isequiv_adjointify cofreglue_susp_map_str).
  - exact cofreglue_susp_map_str_inv.
  - snapply (Susp_ind_FFlr _ _).
    + reflexivity.
    + simpl. exact (merid pt).
    + intro z. simpl.
      lhs napply (whiskerR
                    (ap02 cofreglue_susp_map_str
                       (Susp_rec_beta_merid
                          (H_N := cf_apex reglue_str) (H_S := cf_apex reglue_str) z))
                    _).
      lhs napply (whiskerR (ap_pp cofreglue_susp_map_str _
                              (cfglue reglue_str (wedge_inr (g_idp z)))) 
                    _).
      lhs napply (whiskerR
                    (ap_Vap_comp cofreglue_susp_map_str (cofib reglue_str) _ _
                       @@ cofiber_rec_beta_cfglue (wedge_inr (g_idp z)))
                    _).
      lhs napply (whiskerR (whiskerR (_ @@ _) _) _).
      * simpl. exact (functor_pushout_beta_pglue (f := f) (g := g) (B' := pUnit) z).
      * napply inverse2.
        exact (cofiber_rec_beta_cfglue (wedge_inl (f_idp z))).
      * simpl. lhs napply (concat_pV_p _ (merid pt)).
        lhs napply (concat_1p _ @ concat_p1 _).
        reflexivity.
  - snapply (cofib_retraction_ind _ (const_tt Y) (fun u : Unit => path_unit _ u)).
    + reflexivity.
    + snapply Pushout_ind_FlFr.
      * intro x. simpl. exact ((cfglue reglue_str (wedge_inl x))^).
      * intro y. simpl. exact ((cfglue reglue_str (wedge_inr y))^).
      * intro z. simpl. lhs napply (whiskerR _ _).
        -- lhs napply (ap_compose (ext_glue f_idp g_idp) cofreglue_susp_map_str_inv
                         (pglue z)).
           lhs napply (ap02 cofreglue_susp_map_str_inv (functor_pushout_beta_pglue z)).
           lhs napply (ap02 cofreglue_susp_map_str_inv (concat_p1 _ @ concat_1p _)).
           exact (Susp_rec_beta_merid z).
        -- cbn. lhs napply (concat_pp_V _ _).
           reflexivity.
    + simpl. intro x. lhs napply (transport_paths_Flr (pglue (pushl x)) _);
        lhs napply (whiskerR _ (pglue (pushl x))).
      -- napply (whiskerR (inverse2 _)).
         lhs napply (ap_compose cofreglue_susp_map_str cofreglue_susp_map_str_inv
                       (pglue (pushl x))).
         exact (ap02 cofreglue_susp_map_str_inv
                  (cofiber_rec_beta_cfglue (f := reglue_str) (pushl x))).
      -- simpl. lhs napply (whiskerR (concat_1p _) (pglue (pushl x))).
         exact (concat_Vp (pglue (pushl x))).                 
    + simpl. intro y. lhs napply (transport_paths_Flr (pglue (pushr y)) _).
      lhs napply (whiskerR _ (pglue (pushr y))).
      -- napply (whiskerR (inverse2 _)).
         lhs napply (ap_compose cofreglue_susp_map_str cofreglue_susp_map_str_inv
                       (pglue (pushr y))).
         lhs napply (ap02 cofreglue_susp_map_str_inv
                       (cofiber_rec_beta_cfglue (f := reglue_str) (pushr y))).
         simpl. lhs napply (ap_V cofreglue_susp_map_str_inv (merid pt)).
         lhs napply (inverse2 (Susp_rec_beta_merid pt)).
         napply (inverse2 _).
         lhs napply (whiskerL _ (homotopy_square_r (cfglue reglue_str) wglue)).
         assert (palg_helper : forall {A : Type} {a b c d : A}
                                      (p1 : b = a) {p2 p3 : b = c} (r : p2 = p3) (s : a = d),
                    (p1^ @ p2) @ ((p3^ @ p1) @ s) = s). {
           destruct p1. intros. destruct p2. destruct r. destruct s. reflexivity.
         }
         napply (palg_helper _ _ _ _ _
                   (cfglue (reglue f_idp g_idp) (pushl pt))
                   _ _ _
                   (ap (fun _ => cf_apex reglue_str) wglue)).
         rhs napply (ap_compose (reglue_str) (cofib reglue_str) wglue).
         rhs napply (ap02 (cofib reglue_str) (functor_pushout_beta_pglue pt)).
         cbn. symmetry. napply (ap02 (cofib reglue_str) (concat_p1 _ @ concat_1p _)).
      -- lhs napply (concat_pV_p _ (pglue (pushr y))).
         rewrite inv_V.
         exact (ap_const wglue (cf_apex reglue_str)).
 Qed.

Lemma cofreglue_susp {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}
    : pcofiber (reglue f g) <~>* psusp Z.
Proof.
  snapply Build_pEquiv.
  - exact cofreglue_susp_pmap.
  - exact cofreglue_susp_map_isequiv.
Defined.

(* a couple of useful coherence conditions between cofreglue_susp and ext_glue *)
Section CofReglueCoh.

  Context {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}.

  Lemma cofreglue_susp_extglue_cofib
    : cofreglue_susp o* ptd_cofib (reglue f g) ==* ext_glue f g.
  Proof.
    snapply Build_pHomotopy.
    - snapply Pushout_ind_FlFr.
      + reflexivity.
      + reflexivity.
      + intro z. simpl. rewrite concat_p1. rewrite concat_1p. reflexivity.
    - simpl. rhs napply (concat_p1 _ @ concat_p1 _).
      rewrite concat_1p.
      etransitivity.
      2: {
        symmetry.
        exact (cofiber_rec_beta_cfglue (null := extreglue_nullhmtpy) pt).
      }
      reflexivity.
  Qed.

  Lemma diff_cofreglue_susp_extglue
    : psusp_diff f g o* cofreglue_susp ==* ext_glue_cof (reglue f g).
  Proof.
    snapply Build_pHomotopy.
    - snapply (cofib_retraction_ind _ (const_tt Y) (fun u : Unit => path_unit _ u)).
  Admitted.
  
End CofReglueCoh.
