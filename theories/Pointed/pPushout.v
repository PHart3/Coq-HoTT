From HoTT Require Import Basics.
Require Import Pointed.Core.
Require Import Colimits.Pushout.

Local Open Scope pointed_scope.

(** * Pointed pushouts *)

Definition pPushout {A B C : Type} `{ptB : IsPointed B} (f : A -> B) (g : A -> C) : pType
  := [Pushout f g, pushl ptB].

(** *** Action on maps of spans *)

Definition functor_pPushout
  {A C} {B : pType} {f : A -> B} {g : A -> C}
  {A' C'} {B' : pType} {f' : A' -> B'} {g' : A' -> C'}
  (h : A -> A') (k : B ->* B') (l : C -> C')
  (p : k o f == f' o h) (q : l o g == g' o h) :
  pPushout f g ->* pPushout f' g'.
Proof.
  snapply Build_pMap.
  - napply (functor_pushout h k l p q).
  - simpl.
    apply (ap pushl).
    exact (point_eq k).
Defined.

(** *** The legs of a pointed pushout are pointed. *)

Section PtdLegsPO.

  Context {A B C : pType} {f : A ->* B} {g : A ->* C}.

  Definition ptd_pushl : B ->* pPushout f g
    := Build_pMap pushl 1.

  Definition ptd_pushr : C ->* pPushout f g
    := Build_pMap pushr ((ap pushr (point_eq g))^ @ (pglue pt)^ @ ap pushl (point_eq f)).
  
End PtdLegsPO.
