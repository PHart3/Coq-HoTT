From HoTT Require Import Basics.
Require Import Pointed.Core.
Require Import Homotopy.Cofiber.

Local Open Scope pointed_scope.

(** * Pointed cofibers *)

Definition pCofiber {X Y : pType} (f : X ->* Y)
  := [Cofiber f, cf_apex f].

Definition ptd_cofib {X Y : pType} (f : X ->* Y) : Y ->* pCofiber f
    := Build_pMap (cofib f) ((ap (cofib f) (point_eq f))^ @ cfglue f pt).
