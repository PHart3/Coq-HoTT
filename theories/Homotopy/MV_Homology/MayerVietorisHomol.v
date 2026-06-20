From HoTT Require Import Basics abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup AbHom Biproduct.
Require Import Pointed.Core pPushout pSusp pCofiber.
Require Import Homotopy.Homology SuccessorStructure.

Local Open Scope pointed_scope.
Local Open Scope succ_scope.

(** * The Mayer-Vietoris sequence for homology *)

Generalizable Variables N.

Section MVMaps.

  Context `{HomologyTheory} {C A B : pType} {n : N}.

  (** We begin with the three maps that generate the long sequence. *)

  Definition MV_push_diff : forall {f : C ->* A} {g : C ->* B},
    ab_biprod (C_obj n A) (C_obj n B) $-> C_obj n (ppushout f g)
    := fun f g => ab_biprod_rec
         (fmap (C_obj n) ptd_pushl) (fmap (C_obj n) ptd_pushr).

  Definition MV_po_to_prod : forall (f : C ->* A) (g : C ->* B),
      C_obj n C $-> ab_biprod (C_obj n A) (C_obj n B)
    := fun f g => ab_biprod_corec (fmap (C_obj n) f) (inverse_hom (fmap (C_obj n) g)).

  Definition MV_boundary_map : forall {f : C ->* A} {g : C ->* B},
      C_obj (n .+1) (ppushout f g) $-> C_obj n C
    := fun f g => C_susp C $o fmap (C_obj (n .+1)) (ext_glue f g).

  (** In homology, ext_glue fits into a commuting triangle with the cofiber-suspension equivalence. *)
  Lemma MV_boundary_cof_susp_equiv {f : C ->* A} {g : C ->* B} :
    fmap (C_obj n) (cof_susp_equiv f g) ∘ fmap (C_obj n) (ptd_cofib (reglue f g))
    == fmap (C_obj n) (ext_glue f g).
  Proof.
    napply pointwise_paths_concat.
    + symmetry. exact (fmap_comp (C_obj n) (ptd_cofib (reglue f g)) (cof_susp_equiv f g)).
    + exact (Homol_mor_bpind (ext_glue f g)).
  Qed.

End MVMaps.

(** The full Mayer-Vietoris long sequence *)

Section MVSeq.
  
  Context `{HomologyTheory (N := +Z)} {C A B : pType} (f : C ->* A) (g : C ->* B).

  Definition MV_long_seq_carrier (n : Z3) : AbGroup :=
    match n with
    | (n, inl (inl (inl x))) => Empty_ind _ x
    | (n, inl (inl (inr tt))) => C_obj n (ppushout f g) 
    | (n, inl (inr tt)) => ab_biprod (C_obj n A) (C_obj n B)
    | (n, inr tt) => C_obj n C
    end.
  
  Definition MV_long_seq : forall n, MV_long_seq_carrier (n .+1) ->* MV_long_seq_carrier n.
  Proof.
    intros [n [[[[]|[]]|[]]|[]]]; cbn.
    - exact MV_push_diff.
    - exact (MV_po_to_prod f g).
    - exact MV_boundary_map.
  Defined.
  
End MVSeq.
