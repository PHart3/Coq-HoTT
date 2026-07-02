From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup Biproduct.
Require Import Colimits.Pushout.
Require Import Pointed.Core pCofiber pEquiv.
Require Import Homotopy.Cofiber ExactSequence Wedge.
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
  Context {G H1 H2 : AbGroup}
    {i1 : H1 $-> G}
    {i2 : H2 $-> G}
    {j1 : G $-> H1}
    {j2 : G $-> H2}
    (htpy1 : j1 $o i1 == idmap)
    (htpy2 : j2 $o i2 == idmap)
    (i1_j2_isexact : GrpIsExact i1 j2)
    (i2_j1_isexact : GrpIsExact i2 j1).
  
  Lemma ab_biprod_isequiv : IsEquiv (ab_biprod_corec j1 j2).
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

  Definition ab_biprod_iso : GroupIsomorphism G (ab_biprod H1 H2).
  Proof.
    snapply Build_GroupIsomorphism.
    - apply (ab_biprod_corec j1 j2).
    - exact ab_biprod_isequiv.
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
  Definition cofl_r : pcofiber wedge_inl -> Y.
  Proof.
    snapply cofiber_rec.
    - exact wedge_pr2.
    - exists pt.
      reflexivity.    
  Defined.

  Definition pmap_cofl_r : pcofiber wedge_inl ->* Y
    := Build_pMap cofl_r idpath.
      
  Definition r_cofl : Y -> pcofiber wedge_inl.
  Proof.    
    exact (ptd_cofib wedge_inl o* wedge_inr).
  Defined.  

  Definition pmap_r_cofl : Y ->* pcofiber wedge_inl.
  Proof.
    snapply Build_pMap.
    - apply r_cofl.
    - unfold r_cofl.
      rhs_V apply (point_eq (ptd_cofib wedge_inl)).
      apply (ap (ptd_cofib wedge_inl)).
      apply (point_eq wedge_inr).
  Defined.
      
  Definition cofl_hpty : r_cofl o cofl_r == idmap.
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
        snapply (@dpath_path_FlFr _ _ (r_cofl o cofl_r o (cofib wedge_inl)) _ _ _ wglue _).
        rhs napply concat_p1.
        lhs napply concat_pp_p; lhs napply concat_pp_p; lhs napply concat_pp_p.
        lhs napply concat_1p.
        apply moveR_Vp.
        lhs napply concat_p_Vp.
        apply moveL_Mp; lhs napply concat_Vp.
        rhs apply (ap_compose'
                     (cofl_r o (cofib wedge_inl))
                     r_cofl
                     wglue).
        rhs napply (ap (ap r_cofl) (wedge_rec_beta_wglue _ _)).
        reflexivity.
    - exists ((ap (cofib wedge_inl) wglue)^ @ cfglue wedge_inl pt); simpl.
      intro x.
      napply dpath_path_FFlr.
      lhs napply concat_pV_p.
      lhs napply concat_pp_p.
      apply moveL_pM.
      lhs napply concat_pp_V.
      rhs snapply (ap (ap r_cofl) (cofiber_rec_beta_cfglue (f := pushl) _ x)); cbn.
      reflexivity.
  Defined.
  
  Definition r_cofl_equiv : Y <~> Cofiber wedge_inl.
  Proof.
    snapply equiv_adjointify.
    - apply r_cofl.
    - apply cofl_r.
    - apply cofl_hpty.
    - reflexivity.
  Defined.

  Definition r_cofl_pequiv : Y <~>* pcofiber wedge_inl.
  Proof.
    snapply Build_pEquiv.
    - apply pmap_r_cofl.
    - apply r_cofl_equiv.
  Defined.

  (* From this pointed equivalence and the exactness axiom we get that the sequence of groups X $-> X\/Y $-> Y is exact. *)
  Definition l_to_r_grpisexact : GrpIsExact (fmap (C_obj z) wedge_inl) (fmap (C_obj z) wedge_pr2).
  Proof.
    refine (grpisexact_square_if grp_iso_id grp_iso_id (Homol_pequiv_GroupIsomorphism r_cofl_pequiv) _ _).
    - intro x; reflexivity.
    - lhs_V' tapply (fmap_comp (C_obj z)).
      tapply (fmap2 (C_obj z)).       
      snapply Build_pHomotopy.
      + intro w.
        refine (moveR_equiv_M (wedge_pr2 w) (ptd_cofib wedge_inl w) _). 
        simpl.
        reflexivity.
      + simpl.
        rhs_V napply concat_p_pp; rhs napply concat_1p.
        rhs_V napply concat_p_pp.
        napply moveL_Mp.
        rhs napply concat_pV.
        napply moveR_Vp; rhs napply concat_p1.
        unfold moveR_equiv_M; simpl.
        lhs napply concat_1p.
        lhs napply concat_pp_p; lhs napply concat_pp_p; lhs napply concat_1p.
        lhs napply concat_p_pp; lhs napply concat_pp_V.
        apply (inverse_ap (cofib pushl) _).
    - apply C_exactness.
  Defined.
  
  (* Similarily we have pcofiber wedge_inr <~>* X *)
  Definition cofr_l : pcofiber wedge_inr -> X.
  Proof.
    snapply cofiber_rec.
    - exact wedge_pr1.
    - exists pt.
      reflexivity.
  Defined.

  Definition pmap_cofr_l : pcofiber wedge_inr -> X
    := Build_pMap cofr_l idpath.

  Definition l_cofr : X -> pcofiber wedge_inr.
  Proof.
    exact (ptd_cofib wedge_inr o* wedge_inl).
  Defined.

  Definition pmap_l_cofr : X ->* pcofiber wedge_inr.
  Proof.
    snapply Build_pMap.
    - apply l_cofr.
    - unfold l_cofr.
      rhs_V apply (point_eq (ptd_cofib wedge_inr)).
      apply (ap (ptd_cofib wedge_inr)).
      apply (point_eq wedge_inl).
  Defined.

  Definition cofr_hpty : l_cofr o cofr_l == idmap.
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
        snapply (@dpath_path_FlFr _ _ (l_cofr o cofr_l o (cofib wedge_inr)) _ _ _ wglue _).
        lhs napply concat_1p.
        apply moveL_Mp.
        rhs napply concat_pp_p; rhs napply concat_pp_p.
        rhs napply concat_1p.
        rhs napply concat_p_pp; rhs napply concat_pp_V.
        apply moveR_pM.
        rhs napply concat_pV.
        apply moveR_V1; rhs napply concat_p1.
        rhs apply (ap_compose'
                     (cofr_l o (cofib wedge_inr))
                     l_cofr
                     wglue).
        rhs napply (ap (ap l_cofr) (wedge_rec_beta_wglue _ _)).
        reflexivity.
    - exists ((ap (cofib wedge_inr) wglue) @ cfglue wedge_inr pt); simpl.
      intro y.
      napply dpath_path_FFlr.
      lhs napply concat_pV_p.
      lhs napply concat_pp_p.
      apply moveL_pM.
      lhs napply concat_pp_V.
      rhs snapply (ap (ap l_cofr) (cofiber_rec_beta_cfglue (f := pushr) _ y)); cbn.
      reflexivity.
  Defined.

  Definition l_cofr_equiv : X <~> Cofiber wedge_inr.
  Proof.
    snapply equiv_adjointify.
    - apply l_cofr.
    - apply cofr_l.
    - apply cofr_hpty.
    - reflexivity.    
  Defined.

  Definition l_cofr_pequiv : X <~>* pcofiber wedge_inr.
  Proof.
    snapply Build_pEquiv.
    - apply pmap_l_cofr.
    - apply l_cofr_equiv.
  Defined.

  (* The following sequence is exact, Y $-> X\/Y $-> X *)
  Definition r_to_l_grpisexact : GrpIsExact (fmap (C_obj z) wedge_inr) (fmap (C_obj z) wedge_pr1).
  Proof.
    refine (grpisexact_square_if grp_iso_id grp_iso_id (Homol_pequiv_GroupIsomorphism l_cofr_pequiv) _ _).
    - intro x; reflexivity.
    - lhs_V' tapply (fmap_comp (C_obj z)).
      tapply (fmap2 (C_obj z)).       
      snapply Build_pHomotopy.
      + intro w.
        refine (moveR_equiv_M (wedge_pr1 w) (ptd_cofib wedge_inr w) _). 
        simpl.
        reflexivity.
      + simpl.
        rhs_V napply concat_p_pp; rhs napply concat_1p.
        rhs_V napply concat_p_pp; rhs napply concat_1p.
        rhs napply concat_pV.
        unfold moveR_equiv_M; simpl.
        reflexivity.
    - apply C_exactness.
  Defined.
      
  Theorem homol_preserves_coprod : GroupIsomorphism (C_obj z (X \/ Y)) (ab_biprod (C_obj z X) (C_obj z Y)).
  Proof.
    snapply ab_biprod_iso.
    - exact (fmap (C_obj z) wedge_inl).
    - exact (fmap (C_obj z) wedge_inr).
    - exact (fmap (C_obj z) wedge_pr1).
    - exact (fmap (C_obj z) wedge_pr2).
    - lhs_V' tapply (fmap_comp (C_obj z)).
      tapply (fmap_id (C_obj z)).
    - lhs_V' tapply (fmap_comp (C_obj z)).
      lhs' tapply (fmap2 (C_obj z)).
      + apply wedge_pr2_inr.
      + tapply (fmap_id (C_obj z)).
    - apply l_to_r_grpisexact.
    - apply r_to_l_grpisexact.
  Defined.

End Homol_bin_wedge.
