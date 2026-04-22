From HoTT Require Import Basics abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Pointed.Core pSusp pCofiber.
Require Import SuccessorStructure.

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
      cbn.
      exists ((i1 h1) * (i2 h2)).
      apply (path_prod').
      + set (p := im_sub_ker _ _ i2_j1_isexact (i2 h2) (tr (n:=-1) (h2; idpath (i2 h2)))).
        cbn in p.       
        set (p1 := ap ((j1 (i1 h1))*.) p).
        set (p2 := (grp_homo_op j1 (i1 h1) (i2 h2)) @ p1 @ grp_unit_r (j1 (i1 h1))).
        exact (concat_r (htpy1 h1) p2).
        
      + set (q := im_sub_ker _ _ i1_j2_isexact (i1 h1) (tr (n:=-1) (h1; idpath (i1 h1)))).   
        set (q1 := ap (.*(j2 (i2 h2))) q).
        set (q2 := grp_homo_op j2 (i1 h1) (i2 h2) @ q1 @ grp_unit_l (j2 (i2 h2))).
        exact (concat_r (htpy2 h2) q2).  
    - intro y; destruct y as [y1 y2].
      apply isembedding_istrivial_kernel.
      intro g.
      cbn.
      intro pair_path.
      set (p1 := (ap fst pair_path)); cbn in p1.
      set (p2 := (ap snd pair_path)); cbn in p2.
      set (im_witness := ker_sub_im _ _ i1_j2_isexact g p2).
      cbn in im_witness.
      rapply (Trunc_rec (n:=-1) _ im_witness).
      + napply sig_rec.
        intros h1 wpath.
        rhs_V apply (grp_homo_unit i1).
        rhs_V apply (ap i1 p1).
        rhs_V apply (ap (i1 $o j1) wpath).
        rhs apply (ap i1 (htpy1 h1)).
        rhs apply wpath.
        reflexivity.
  Qed.

  (*
  Lemma top_th_lemma
    {X Y : pType}
    : (pcofiber wedge_inl) <~> Y.
    
  Qed.
  *)
End Homol_bin_wedge.
