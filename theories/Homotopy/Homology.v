From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Pointed.Core pSusp pCofiber.

Local Open Scope pointed_scope.

(** * Generalized homology theories *)

Generalizable Variables Z.

Record HomologyTheory `{Integers Z} := {
    C_obj : Z -> pType -> AbGroup;
    C_0ftor :: forall z, Is0Functor (C_obj z);
    C_1ftor : forall z, Is1Functor (C_obj z);
    C_exactness : forall {n : Z} {X Y : pType} (f : X ->* Y),
      GrpIsExact (fmap (C_obj n) f) (fmap (C_obj n) (ptd_cofib f));
    C_susp : forall {n : Z} (X : pType),
      GroupIsomorphism (C_obj (1 + n) (psusp X)) (C_obj n X);
    C_susp_fmap : forall {n : Z} {X Y : pType} (f : X ->* Y) (x : C_obj (1 + n) (psusp X)),
      fmap (C_obj n) f ∘ C_susp X == C_susp Y ∘ fmap (C_obj (1 + n)) (fmap psusp f);
    }.
