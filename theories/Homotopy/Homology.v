From HoTT Require Import Basics abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import SuccessorStructure.
Require Import Colimits.Pushout.
Require Import Pointed.Core pCofiber pEquiv pSusp.
Require Import Homotopy.Cofiber Wedge.

Local Open Scope succ_scope.
Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

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

(* Since we do not assume the additivity axiom for homology theories, we prove binary additivity from the exactness axiom, that is, H(X \/ Y) <~> H(X) x H(Y) *)
Section Homol_bin_wedge.
  (* This is a necessary sublemma about groups. Suppose we have the following diagram of groups,

             i1           i2
       H1 --------> G <-------- H2
          <--------   -------->
             j1           j2

  with homotopies j1 o i1 ~ id and j2 o i2 ~ id and that the following sequences are exact,

           i1      j2                  j1      i2
       H1 ----> G ----> H2        H1 <---- G <---- H2

  then there is a group isomorphism (j1,j2) : G <~> H1xH2. *)
  Lemma grp_th_lemma
    {G H1 H2 : Group}
    {i1 : H1 $-> G}
    {i2 : H2 $-> G}
    {j1 : G $-> H1}
    {j2 : G $-> H2}
    (htpy1 : j1 $o i1 == idmap)
    (htpy2 : j2 $o i2 == idmap)
    (i1_j2_isexact : GrpIsExact i1 j2)
    (i2_j1_isexact : GrpIsExact i2 j1)
    : IsEquiv (grp_prod_corec j1 j2).
  Proof.
    apply isequiv_surj_emb.
    - apply BuildIsSurjection.
      intro h1h2; destruct h1h2 as [h1 h2].
      apply tr.
      exists ((i1 h1) * (i2 h2)).
      apply (path_prod').
      + lhs apply (grp_homo_op j1 (i1 h1) (i2 h2)).
        lhs apply (ap (.*(j1 (i2 h2))) (htpy1 h1)).
        rhs_V apply (grp_unit_r h1).
        apply (grp_cancelL h1).
        exact (im_sub_ker _ _ i2_j1_isexact (i2 h2) (tr (h2; idpath (i2 h2)))).
      + lhs apply (grp_homo_op j2 (i1 h1) (i2 h2)).
        lhs apply (ap ((j2 (i1 h1))*.) (htpy2 h2)).
        rhs_V apply (grp_unit_l h2).
        apply (grp_cancelR h2).
        exact (im_sub_ker _ _ i1_j2_isexact (i1 h1) (tr (h1; idpath (i1 h1)))).
    - intro y; destruct y as [y1 y2].
      apply isembedding_istrivial_kernel.
      intros g pair_path.
      pose (p2 := (ap snd pair_path)).
      pose (im_witness := ker_sub_im _ _ i1_j2_isexact g p2).
      rapply (Trunc_rec _ im_witness).
      napply sig_rec.
      intros h1 wpath.
      rhs_V apply (grp_homo_unit i1).
      rhs_V apply (ap (i1 o fst) pair_path).
      rhs_V apply (ap (i1 $o j1) wpath).
      rhs apply (ap i1 (htpy1 h1)).
      symmetry; apply wpath.
  Qed.

(*  Definition grp_prod_iso
    {G H1 H2 : Group}
    {i1 : H1 $-> G}
    {i2 : H2 $-> G}
    {j1 : G $-> H1}
    {j2 : G $-> H2}
    (htpy1 : j1 o i1 == idmap)
    (htpy2 : j2 o i2 == idmap)
    (i1_j2_isexact : GrpIsExact i1 j2)
    (i2_j1_isexact : GrpIsExact i2 j1)
    : GroupIsomorphism G (grp_prod H1 H2) := Build_GroupIsomorphism G (grp_prod H1 H2) (grp_prod_corec j1 j1) _.
  Proof
    apply grp_th_lemma.
  Defined.
  *)

  Definition cof_to_Y {X Y : pType} : pcofiber (@wedge_inl X Y) -> Y.
  Proof.
    snapply Pushout_rec.
    - exact wedge_pr2.
    - intro pnt; exact (point Y).
    - intro x; reflexivity.    
  Defined.

  Definition Y_to_cof {X Y : pType} : Y -> pcofiber (@wedge_inl X Y).
  Proof.
    intro y.
    apply (cofib wedge_inl).
    apply (wedge_inr y).
  Defined.

(*  Definition cof_to_Y_to_cof
    {X Y : pType}
    {f : pcofiber (@wedge_inl X Y) -> Y}
    {g : Y -> pcofiber (@wedge_inl X Y)}
    : g o f == idmap.
  Proof.
    snapply cofiber_ind.
    - cbn.
      snapply wedge_ind.
      + intro x.
        cbn.
        
        pose (mycfglue := cfglue (@wedge_inl X Y) x). 
        pose (mywglue := ap (cofib wedge_inl) (@wglue X Y)).
        rhs apply mycfglue.

        
  Definition cof_wedge_inl_cod_equiv {X Y : pType} : pcofiber (@wedge_inl X Y) <~> Y.
  Proof.
    snapply Build_Equiv.
     (* pose (f := Pushout_rec Y wedge_pr2). *)
    - exact f.
    - snapply Build_IsEquiv.
      + exact g.
      + reflexivity.
      +
  Defined.

  Definition cof_wedge_inl_cod_pequiv := term.
  Proof.
    snapply Build_pEquiv'.
  Defined
  *)       
End Homol_bin_wedge.
