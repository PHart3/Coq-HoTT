From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Colimits.Pushout.
Require Import Pointed.Core pCofiber pEquiv.
Require Import Homotopy.Cofiber Wedge.
Require Import Homology.Core.
Require Import Types.Paths.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

Generalizable Variable Z.

(* Since we do not assume the additivity axiom for homology theories, we prove binary additivity from the exactness axiom, that is, H(X \/ Y) <~> H(X) x H(Y) *)
Section Alg_Homol_bin_wedge.
  (* This is a necessary sublemma about groups. Suppose we have the following diagram of groups,

             i1           i2
       H1 --------> G <-------- H2
          <--------   -------->
             j1           j2

  with homotopies j1 o i1 ~ id and j2 o i2 ~ id and that the following sequences are exact,

           i1      j2                  j1      i2
       H1 ----> G ----> H2        H1 <---- G <---- H2

  then there is a group isomorphism (j1,j2) : G <~> H1xH2. *)
  Context {G H1 H2 : Group}
    {i1 : H1 $-> G}
    {i2 : H2 $-> G}
    {j1 : G $-> H1}
    {j2 : G $-> H2}
    (htpy1 : j1 $o i1 == idmap)
    (htpy2 : j2 $o i2 == idmap)
    (i1_j2_isexact : GrpIsExact i1 j2)
    (i2_j1_isexact : GrpIsExact i2 j1).
  
  Lemma grp_prod_isequiv : IsEquiv (grp_prod_corec j1 j2).
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

  Definition grp_prod_iso : GroupIsomorphism G (grp_prod H1 H2).
  Proof.
    snapply Build_GroupIsomorphism.
    - exact (grp_prod_corec j1 j2).
    - exact grp_prod_isequiv.
  Defined.

End Alg_Homol_bin_wedge.


Section Homol_bin_wedge.
  Context {X Y : pType} `{Integers Z} {z : Z} {C : HomologyTheory}.
  Local Definition wedge_inl := @wedge_inl X Y.
  Local Definition wedge_inr := @wedge_inr X Y.
  Local Definition wedge_pr1 := @wedge_pr1 X Y.
  Local Definition wedge_pr2 := @wedge_pr2 X Y.
  Local Definition wglue := @wglue X Y.

  (* For the map wedge_inl : X -> X\/Y, there is a pointed equivalence, pcofiber wedge_inl <~>* Y. *)
  Definition cofl_to_r : pcofiber wedge_inl -> Y.
  Proof.
    snapply cofiber_rec.
    - exact wedge_pr2.
    - exists pt.
      intro x.
      reflexivity.
  Defined.

 Definition r_to_cofl : Y -> pcofiber wedge_inl.
  Proof.
    exact (cofib wedge_inl o wedge_inr).
  Defined.

  Definition cofl_hpty : r_to_cofl o cofl_to_r == idmap.
  Proof.
    snapply cofiber_ind.
    - snapply wedge_ind.
      + intro x; simpl.
        rhs apply (cfglue wedge_inl x).
        rhs_V apply (cfglue wedge_inl pt).
        rhs apply (ap (cofib wedge_inl) wglue).
        reflexivity.
      + reflexivity.
      + simpl.
        snapply (@dpath_path_FlFr _ _ (r_to_cofl o cofl_to_r o (cofib wedge_inl)) _ _ _ wglue _).
        rhs napply concat_p1.
        lhs napply concat_pp_p; lhs napply concat_pp_p; lhs napply concat_pp_p.
        lhs napply concat_1p.
        apply moveR_Vp.
        lhs napply concat_p_Vp.
        apply moveL_Mp; lhs napply concat_Vp.
        rhs apply (ap_compose'
                     (cofl_to_r o (cofib wedge_inl))
                     r_to_cofl
                     wglue).
        rhs napply (ap (ap r_to_cofl) (wedge_rec_beta_wglue _ _)).
        reflexivity.
    - exists ((ap (cofib wedge_inl) wglue)^ @ cfglue wedge_inl pt); simpl.
      intro x.
      napply dpath_path_FFlr.
      lhs napply concat_pV_p.
      lhs napply concat_pp_p.
      apply moveL_pM.
      lhs napply concat_pp_V.
      rhs snapply (ap (ap r_to_cofl) (cofiber_rec_beta_cfglue (f := pushl) _ x)); cbn.
      reflexivity.
  Defined.

  Definition cofl_r_equiv : Cofiber wedge_inl <~> Y.
  Proof.
    snapply equiv_adjointify.
    - exact cofl_to_r.
    - exact r_to_cofl.
    - reflexivity.
    - exact cofl_hpty.
  Defined.

  Definition cofl_r_pequiv : pcofiber wedge_inl <~>* Y.
  Proof.
    snapply Build_pEquiv'.
    - exact cofl_r_equiv.
    - reflexivity.
  Defined.

  (* Similarily we have pcofiber wedge_inr <~>* X *)
  Definition cofr_to_l : pcofiber wedge_inr -> X.
  Proof.
    snapply cofiber_rec.
    - exact wedge_pr1.
    - exists pt.
      reflexivity.
  Defined.

  Definition l_to_cofr : X -> pcofiber wedge_inr.
  Proof.
    exact (cofib wedge_inr o wedge_inl).
  Defined.

  Definition cofr_hpty : l_to_cofr o cofr_to_l == idmap.
  Proof.
    snapply cofiber_ind.
    - snapply wedge_ind.
      + reflexivity.
      + intro y; simpl.
        rhs apply (cfglue wedge_inr y).
        rhs_V apply (cfglue wedge_inr pt).
        rhs_V apply (ap (cofib wedge_inr) wglue).
        reflexivity.
      + simpl.
        snapply (@dpath_path_FlFr _ _ (l_to_cofr o cofr_to_l o (cofib wedge_inr)) _ _ _ wglue _).
        lhs napply concat_1p.
        apply moveL_Mp.
        rhs napply concat_pp_p; rhs napply concat_pp_p.
        rhs napply concat_1p.
        rhs napply concat_p_pp; rhs napply concat_pp_V.
        apply moveR_pM.
        rhs napply concat_pV.
        apply moveR_V1; rhs napply concat_p1.
        rhs apply (ap_compose'
                     (cofr_to_l o (cofib wedge_inr))
                     l_to_cofr
                     wglue).
        rhs napply (ap (ap l_to_cofr) (wedge_rec_beta_wglue _ _)).
        reflexivity.
    - exists ((ap (cofib wedge_inr) wglue) @ cfglue wedge_inr pt); simpl.
      intro y.
      napply dpath_path_FFlr.
      lhs napply concat_pV_p.
      lhs napply concat_pp_p.
      apply moveL_pM.
      lhs napply concat_pp_V.
      rhs snapply (ap (ap l_to_cofr) (cofiber_rec_beta_cfglue (f := pushr) _ y)); cbn.
      reflexivity.
  Defined.

  Definition cofr_l_equiv : Cofiber wedge_inr <~> X.
  Proof.
    snapply equiv_adjointify.
    - exact cofr_to_l.
    - exact l_to_cofr.
    - reflexivity.
    - exact cofr_hpty.
  Defined.

  Definition cofr_l_pequiv : pcofiber wedge_inr <~>* X.
  Proof.
    snapply Build_pEquiv'.
    - exact cofr_l_equiv.
    - reflexivity.
  Defined.

  (*
  Definition HomolGrpIso : GroupIsomorphism (C_obj z (pcofiber wedge_inl)) (C_obj z Y).
  Proof.
    snapply Build_GroupIsomorphism.
    - exact (fmap (C_obj z) cofl_r_pequiv).
    - snapply Build_IsEquiv.
      + exact (fmap (C_obj z) r_to_cofl).
      
  Definition l_to_r_isexact : GrpIsExact (fmap (C_obj z) wedge_inl) (fmap (C_obj z) wedge_pr2).
  Proof.
    destruct (C_exactness (n:=z) wedge_inl).
    apply Build_GrpIsExact.
    - intros w im; simpl.
      
      pose (im_sub_ker w im); simpl in s.
      pose (fmap (C_obj z) cofl_r_pequiv).
      apply h.
*)
      
  Theorem homol_preserves_coprod : GroupIsomorphism (C_obj z (X \/ Y)) (grp_prod (C_obj z X) (C_obj z Y)).
  Proof.
    snapply grp_prod_iso.
    - exact (fmap (C_obj z) wedge_inl).
    - exact (fmap (C_obj z) wedge_inr).
    - exact (fmap (C_obj z) wedge_pr1).
    - exact (fmap (C_obj z) wedge_pr2).
    - tapply transitive_pointwise_paths.
      + apply symmetric_pointwise_paths.
        exact (fmap_comp (C_obj z) wedge_inl wedge_pr1).
      +
        (* apply something like fmap2 so we can prove
wpr1 o winl == idmap *)
        pose (ap2 (fmap (C_obj)) wedge_pr1_inl).
        pose (fmap2 (C_obj z) _ _ wedge_pr1_inl).
        exact wedge_pr1_inl.
      

End Homol_bin_wedge.                     
*)
