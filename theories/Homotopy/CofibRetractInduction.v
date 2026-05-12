From HoTT Require Import Basics.
Require Import Types.Paths.
Require Import Homotopy.Cofiber.
Require Import Colimits.Pushout.

(** Consider a span where one of the legs has a retraction and take any function h out of the span's pushout.
    We have a general induction principle for the cofiber of h that avoids the higher coherence datum.  *)

Section CofRetractInd.

  Context {X Y Z T : Type} {f : Z -> X} {g : Z -> Y} {h : Pushout f g -> T}.

  (* the short induction principle *)
  Lemma cofib_retraction_ind (P : Cofiber h -> Type) (r : Y -> Z) (retr : r o g == idmap)
    (base_s : P (cf_apex h)) (right_s : forall t, P (cofib h t))
    (glue_s_l : forall x, transport P (pglue (pushl x)) (right_s (h (pushl x))) = base_s)
    (glue_s_r : forall y, transport P (pglue (pushr y)) (right_s (h (pushr y))) = base_s)
    : forall (c : Cofiber h), P c.
  Proof.
    snapply cofiber_ind.
    - exact right_s.
    - exists base_s.
      snapply Pushout_ind.
      + cbn. exact glue_s_l.
      + cbn. intro y.
        pose (base_s_loop :=
                (fun z => (glue_s_r (g z))^
                            @ (ap (fun v => (transport P (pglue v) (right_s (h v)) :> P (cf_apex h)))
                                 (pglue z))^
                              @ glue_s_l (f z)) :
                Z -> base_s = base_s).
        exact (glue_s_r y @ base_s_loop (r y)).
      + intro z.
        lhs napply (transport_paths_Fl (pglue z) (glue_s_l (f z))). cbn.
        rhs napply (whiskerL (glue_s_r (g z))).
        * rhs napply (concat_p_Vp _ _). reflexivity.
        * lhs napply (ap (fun w =>
                            (((glue_s_r (g w))^
                                @ (ap (fun v : Pushout f g => (transport P (pglue v) (right_s (h v)) :>
                                                                 P (cf_apex h)))
                                    (pglue w))^) @
                              glue_s_l (f w)) :> base_s = base_s)
                        (retr z)).
          lhs napply (concat_pp_p _ _ _).
          reflexivity.
  Defined.

  (* β-rule for the preceding induction principle *)
  Definition cofib_retraction_ind_beta
    {r : Y -> Z} {retr : r o g == idmap} {P : Cofiber h -> Type}
    {base_s : P (cf_apex h)} {right_s : forall t, P (cofib h t)}
    {glue_s_l : forall x, transport P (pglue (pushl x)) (right_s (h (pushl x))) = base_s}
    {glue_s_r : forall y, transport P (pglue (pushr y)) (right_s (h (pushr y))) = base_s}
    (x : X)
    : apD (cofib_retraction_ind P r retr base_s right_s glue_s_l glue_s_r) (cfglue h (pushl x)) = glue_s_l x
    := cofiber_ind_beta_cfglue (pushl x).
    
End CofRetractInd.
