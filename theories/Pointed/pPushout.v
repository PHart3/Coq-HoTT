From HoTT Require Import Basics Types.
Require Import Pointed.Core pSusp.
Require Import Colimits.Pushout.
Require Import Homotopy.Wedge Suspension.
Require Import WildCat.Core WildCat.Universe.

Local Open Scope pointed_scope.

(** * Pointed pushouts *)

Definition ppushout {A C : Type} {B : pType} (f : A -> B) (g : A -> C) : pType
  := [Pushout f g, pushl pt].

(** *** Action on maps of spans *)

Definition functor_ppushout
  {A C} {B : pType} {f : A -> B} {g : A -> C}
  {A' C'} {B' : pType} {f' : A' -> B'} {g' : A' -> C'}
  (k : B ->* B') (h : A -> A') (l : C -> C')
  (p : k o f == f' o h) (q : l o g == g' o h) :
  ppushout f g ->* ppushout f' g'.
Proof.
  snapply Build_pMap.
  - napply (functor_pushout h k l p q).
  - simpl.
    exact (ap pushl (point_eq k)).
Defined.

(** *** The legs of a pointed pushout are pointed. *)

Section PtdLegsPO.

  Context {A B C : pType} {f : A ->* B} {g : A ->* C}.

  Definition ptd_pushl : B ->* ppushout f g
    := Build_pMap pushl 1.

  Definition ptd_pushr : C ->* ppushout f g
    := Build_pMap pushr ((ap pushr (point_eq g))^ @ (pglue pt)^ @ ap pushl (point_eq f)).
  
End PtdLegsPO.

(** *** Some useful span maps *)

Section SpanTransform.
  
  Context {X Y Z : pType} (f : Z ->* X) (g : Z ->* Y).

  Definition reglue : X \/ Y ->* ppushout f g
    := functor_ppushout pmap_idmap (fun _ => pt) pmap_idmap
         (fun _ => (point_eq f)^) (fun _ => (point_eq g)^) .

  Definition ext_glue : ppushout f g ->* psusp Z.
  Proof.
    apply (functor_ppushout (B' := pUnit) pconst idmap (const_tt Y)).
    - intros. reflexivity.
    - intros. reflexivity.
  Defined.
  
End SpanTransform.

(** *** Symmetry of pointed pushouts *)

Section PPushoutSym.
  
  Context {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}.

  Definition ppushout_sym_map : ppushout f g ->* ppushout g f.
  Proof.
    exists pushout_sym_map. cbn.
    lhs_V napply (ap pushr).
    - exact (point_eq f).
    - lhs_V napply (pglue pt).
      exact (ap pushl (point_eq g)).
  Defined.
  
  Definition ppushout_sym : ppushout f g <~>* ppushout g f.
  Proof.
    snapply Build_pEquiv.
    - exact ppushout_sym_map.
    - cbn. exact (equiv_isequiv pushout_sym).
  Defined.

End PPushoutSym.

(** *** We have a "diff" map that computes Susp(f), up to a flip, on each summand of X \/ Y. *)

Section PSuspDiff.

  Context {X Y Z : pType} (f : Z ->* X) (g : Z ->* Y).
  
  Definition psusp_diff : psusp Z ->* psusp (X \/ Y).
  Proof.
    snapply Build_pMap.
    - snapply Susp_rec.
      + exact North.
      + exact North.
      + intro z. exact (merid (wedge_inl (f z)) @ (merid (wedge_inr (g z)))^).
    - reflexivity.
  Defined.

  Definition psusp_flip : psusp Z ->* psusp Z
    := ppushout_sym_map
         (f := Build_pMap (B := pUnit) (const_tt Z) idpath)
         (g := Build_pMap (B := pUnit) (const_tt Z) idpath).
  
  Lemma psusp_diff_pr1 : fmap psusp wedge_pr1 o* psusp_diff ==* fmap psusp f.
  Proof.
    snapply Build_pHomotopy.
    - snapply Susp_ind_FlFr.
      + reflexivity.
      + simpl. exact (merid pt).
      + intro z. cbn.
        lhs napply
          (whiskerR (ap_compose _ (functor_susp (wedge_rec' idmap (const pt) idpath)) (merid z)) _).
        lhs napply
          (whiskerR (ap02 (functor_susp (wedge_rec' idmap (const pt) idpath)) (Susp_rec_beta_merid z)) _).
        lhs napply (whiskerR (ap_pV _ (merid (pushl (f z))) (merid (pushr (g z)))) _).
        lhs napply (whiskerR
                      (Susp_rec_beta_merid (pushl (f z))
                         @@ ap inverse (Susp_rec_beta_merid (pushr (g z)))) _).
        simpl. lhs napply (concat_pV_p (merid (f z)) _).
        rhs napply (concat_1p (ap (functor_susp f) (merid z)) @ Susp_rec_beta_merid z).
        reflexivity.
    - reflexivity.
  Qed.

  Lemma psusp_diff_pr2 : fmap psusp wedge_pr2 o* psusp_diff ==* fmap psusp g o* psusp_flip.
  Proof.
    snapply Build_pHomotopy.
    - snapply Susp_ind_FlFr.
      + simpl. exact (merid pt).
      + reflexivity.
      + intro z. cbn.
        lhs napply
          (whiskerR (ap_compose _ (functor_susp (wedge_rec' (const pt) idmap idpath)) (merid z)) _).
        lhs napply
          (whiskerR (ap02 (functor_susp (wedge_rec' (const pt) idmap idpath)) (Susp_rec_beta_merid z)) _).
        lhs napply (whiskerR (ap_pV _ (merid (pushl (f z))) (merid (pushr (g z)))) _).
        lhs napply (whiskerR
                      (Susp_rec_beta_merid (pushl (f z))
                         @@ ap inverse (Susp_rec_beta_merid (pushr (g z)))) _).
        simpl. rhs napply (whiskerL _ (ap_compose pushout_sym_map (functor_susp g) (merid z))).
        rhs napply (whiskerL _ (ap02 (functor_susp g)
                                  (Pushout_rec_beta_pglue (Susp Z) _ _ (fun z : Z => (pglue z)^) z))).
        rhs napply (whiskerL _ (ap_V (functor_susp g) (pglue z) @ ap inverse (Susp_rec_beta_merid z))).
        lhs napply (concat_p1 _).
        reflexivity.
    - simpl. rhs napply (concat_1p _ @ ap inverse (concat_p1 _)).
      rhs napply (ap inverse (ap_pp (functor_susp g) idpath ((pglue pt)^ @ 1) @ concat_1p _)).
      rhs napply (ap inverse (ap_Vp (functor_susp g) (merid pt) idpath @ concat_p1 _) @ inv_V _).
      rhs napply (Susp_rec_beta_merid pt).
      rhs napply (ap merid (point_eq g)).
      reflexivity.    
  Qed.
        
End PSuspDiff.
