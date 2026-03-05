From HoTT Require Import Basics Types WildCat.Core.
Require Import Groups.Group Groups.Subgroup.

Local Open Scope predicate_scope.

(** * Exact sequences of groups *)

Declare Scope grpisexact_scope.
Local Open Scope grpisexact_scope.

Record GrpIsExact {A B C : Group} (i : A $-> B) (f : B $-> C) :=
  Build_GrpIsExact {
      im_sub_ker : grp_image i ⊆ grp_kernel f ;
      ker_sub_im : grp_kernel f ⊆ grp_image i ;
    }.

