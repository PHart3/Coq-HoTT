From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup AbHom Biproduct.
Require Import Pointed.Core pPushout pSusp pCofiber.
Require Import Homotopy.Homology.Core.

Local Open Scope pointed_scope.

(** * The Mayer-Vietoris sequence for homology *)

Generalizable Variables Z.

Section MVHom.

  Context `{Hom : HomologyTheory} {C A B : pType} {n : Z} `{Funext}.

  (** We begin with the three maps that generate the long sequence. *)
  
  Definition MV_boundary_map : forall {f : C ->* A} {g : C ->* B},
      C_obj (1 + n) (ppushout f g) $-> C_obj n C
    := fun f g => C_susp C $o fmap (C_obj (1 + n)) ext_glue.

  Definition MV_push_diff : forall {f : C ->* A} {g : C ->* B},
    ab_biprod (C_obj n A) (C_obj n B) $-> C_obj n (ppushout f g)
    := fun f g => ab_biprod_rec
         (fmap (C_obj n) ptd_pushl) (inverse_hom (fmap (C_obj n) ptd_pushr)).

  Definition MV_po_to_prod : forall (f : C ->* A) (g : C ->* B),
      C_obj n C $-> ab_biprod (C_obj n A) (C_obj n B)
    := fun f g => ab_biprod_corec (fmap (C_obj n) f) (fmap (C_obj n) g).

  (** In homology, ext_glue fits into a commuting triangle with the cofiber-suspension equivalence. *)
  Lemma MV_boundary_cof_susp_equiv {f : C ->* A} {g : C ->* B} :
    fmap (C_obj n) (cof_susp_equiv f g) ∘ fmap (C_obj n) (ptd_cofib reglue) == fmap (C_obj n) ext_glue.
  Proof.
    napply pointwise_paths_concat.
    + symmetry. exact (fmap_comp (C_obj n) (ptd_cofib reglue) (cof_susp_equiv f g)).
    + exact (Homol_mor_bpind ext_glue).
  Qed.

End MVHom.

