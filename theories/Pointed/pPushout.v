From HoTT Require Import Basics Types.
Require Import Pointed.Core pSusp.
Require Import Colimits.Pushout.
Require Import Homotopy.Wedge.

Local Open Scope pointed_scope.

(** * Pointed pushouts *)

Definition pPushout {A C : Type} {B : pType} (f : A -> B) (g : A -> C) : pType
  := [Pushout f g, pushl pt].

(** *** Action on maps of spans *)

Definition functor_pPushout
  {A C} {B : pType} {f : A -> B} {g : A -> C}
  {A' C'} {B' : pType} {f' : A' -> B'} {g' : A' -> C'}
  (k : B ->* B') (h : A -> A') (l : C -> C')
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

(** *** Some useful span maps. *)

Section SpanTransform.
  
  Context {X Y Z : pType} {f : Z ->* X} {g : Z ->* Y}.

  Definition reglue : X \/ Y ->* pPushout f g
    := functor_pPushout pmap_idmap (fun _ => pt) pmap_idmap
         (fun _ => (point_eq f)^) (fun _ => (point_eq g)^) .

  Definition ext_glue : pPushout f g ->* psusp Z.
  Proof.
    apply (functor_pPushout (B' := pUnit) pconst idmap (const_tt Y)).
    - intros. reflexivity.
    - intros. reflexivity.
  Defined.
  
End SpanTransform.
