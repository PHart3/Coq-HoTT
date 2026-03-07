From HoTT Require Import Basics Classes.interfaces.integers abstract_algebra.
From HoTT.WildCat Require Import Core Universe.
Require Import Groups.Group ExactSeq.
Require Import AbGroups.AbelianGroup.
Require Import Pointed.Core pSusp pCofiber.

Local Open Scope pointed_scope.

(** * Generalized homology theories *)

Generalizable Variables Z.

Record HomologyTheory `{Integers Z} := {
    C : Z -> pType -> AbGroup;
    C_0ftor : forall z, Is0Functor (C z);
    C_1ftor : forall z, Is1Functor (C z);
    C_exactness : forall {z : Z} {X Y : pType} (f : X ->* Y),
      GrpIsExact (fmap (C z) f) (fmap (C z) (ptd_cofib f));
    C_susp : forall {z : Z} (X : pType), GroupIsomorphism (C (1 + z) (psusp X)) (C z X);
    C_susp_fmap : forall {z : Z} {X Y : pType} (f : X ->* Y) (x : C (1 + z) (psusp X)),
      fmap (C z) f ∘ C_susp X == C_susp Y ∘ fmap (C (1 + z)) (fmap psusp f);
    }.


