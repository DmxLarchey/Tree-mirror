(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Wellfounded.

Require Import bt env fun_defs.

Set Implicit Arguments.

Local Notation "e ⇢ x" := (@get_env _ _ e x).
Local Notation "e ⦃  x ⇠ v ⦄" := (@set_env _ _ Var_eq_dec e x v).

Section mirror.

  Variables (u x y z : Var) (Hxy : x <> y) (Hux : x <> u) (Huy : y <> u).
  Variable (p : Fun).

  Definition fe_mirror := MATCH £u WITH ø⇒ø OR x#y⇒CALL p ON £y#CALL p ON £x.

  Variable (param : Fun -> Var)     (Hparam : param p = u) 
           (body : Fun -> fun_expr) (Hbody : body p = fe_mirror).

  Notation "f // s ~~> v" := (fun_sem param body f s v).

  Fact fe_mirror_spec_1 f e a b : f // e ~~> a -> a ⋈ b -> CALL p ON f // e ~~> b.
  Proof.
    intros H1 H2; revert H2 f e H1.
    induction 1 as [ | a b c d H1 IH1 H2 IH2 ]; intros f e H3;
      constructor 7 with (1 := H3);
      rewrite Hparam, Hbody; unfold fe_mirror.
    + constructor 4.
      * apply fs_var; rew env.
      * constructor.
    + constructor 5 with a c.
      * apply fs_var; rew env.
      * constructor 3.
        - apply IH2, fs_var; rew env.
        - apply IH1, fs_var; rew env.
  Qed.

  Hint Resolve btm_spec.

  Fact fe_mirror_halt f e a : f // e ~~> a -> CALL p ON f // e ~~> btm a.
  Proof.
    intros H; apply fe_mirror_spec_1 with (1 := H); auto.
  Qed.

  Fact fe_mirror_spec_2 f e a b : f // e ~~> a -> CALL p ON f // e ~~> b <-> a ⋈ b.
  Proof.
    intros H1; split.
    + intros H2.
      rewrite (fun_sem_det H2 (fe_mirror_halt H1)); auto.
    + apply fe_mirror_spec_1; auto.
  Qed.

  Theorem fe_mirror_spec e : CALL p ON £z // e ~~> btm (e⇢z).
  Proof. apply fe_mirror_halt; constructor. Qed.

  Reserved Notation "x // t ▹ y" (at level 70, no associativity).

  Inductive bt_subst (t : bt) : bt -> bt -> Prop :=
    | in_bts_0 : ω // t ▹ t
    | in_bts_1 : forall a a' b b', a // t ▹ a' -> b // t ▹ b' -> ⟨a,b⟩ // t ▹ ⟨a',b'⟩
  where "x // t ▹ y" := (bt_subst t x y).

  Variable (f_subst : Fun).

  Definition fe_subst := 
    MATCH £u WITH 
         ø   ⇒ ø 
      OR x#u ⇒ MATCH £x WITH
           ø   ⇒ £u 
        OR x#y ⇒ (CALL f_subst ON (£x#£u)#CALL f_subst ON (£y#£u)).

  Variables (param_subst : param f_subst = u) 
            (body_subst  : body f_subst = fe_subst).

  Fact fe_subst_spec f e a t a' : a // t ▹ a' -> f // e ~~> ⟨a,t⟩ 
                                              -> CALL f_subst ON f // e ~~> a'.
  Proof.
    intros H1; revert H1 f e.
    induction 1 as [ | a a' b b' H1 IH1 H2 IH2 ]; intros f e H;
      constructor 7 with (1 := H); rewrite param_subst, body_subst; unfold fe_subst.
    + constructor 5 with ω t.
      1: apply fs_var; rew env.
      constructor 4; apply fs_var; rew env.
    + constructor 5 with ⟨a,b⟩ t.
      1: apply fs_var; rew env.
      constructor 5 with a b.
      1: apply fs_var; rew env.
      constructor 3.
      * apply IH1; constructor 3; apply fs_var; rew env.
      * apply IH2; constructor 3; apply fs_var; rew env.
  Qed.

End mirror.

Section bt_list.

  Variables (u x y z : Var) (Hxy : x <> y) (Hux : u <> x) (Huy : u <> y).
  Variable (f_app f_roll f_rev f_rev_aux : Fun).

  Definition fe_app := 
    MATCH £u WITH 
         ø⇒ø 
    OR x#u⇒MATCH £x WITH
           ø⇒£u
      OR x#y⇒£x#CALL f_app ON (£y#£u).

  Definition fe_roll := 
    MATCH £u WITH 
         ø⇒ø 
    OR x#y⇒CALL f_app ON (£y#(£x#ø)).

(*  Definition fe_rev := 
    MATCH £u WITH 
         ø⇒ø 
    OR x#y⇒CALL f_app ON (CALL f_rev ON £y#(£x#ø)). *)

  Definition fe_rev_aux :=
    MATCH £u WITH
         ø⇒ø 
    OR u#x⇒MATCH £x WITH
           ø⇒£u
      OR y#x⇒CALL f_rev_aux ON ((£y#£u)#£x).

  Definition fe_rev := CALL f_rev_aux ON (ø#£u).

  Variable (param : Fun -> Var)     
           (body : Fun -> fun_expr) 
           (Hparam_app : param f_app = u) (Hbody_app : body f_app = fe_app)
           (Hparam_roll : param f_roll = u) (Hbody_roll : body f_roll = fe_roll)
           (Hparam_rev : param f_rev = u) (Hbody_rev : body f_rev = fe_rev)
           (Hparam_rev_aux : param f_rev_aux = u) (Hbody_rev_aux : body f_rev_aux = fe_rev_aux).

  Notation "f // s ~~> v" := (fun_sem param body f s v).

  Fact fe_app_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL f_app ON f // e ~~> bt_app a b.
  Proof.
    revert f e.
    induction a as [ | t _ a IHa ]; intros f e H.
    + constructor 7 with (1 := H).
      rewrite Hparam_app, Hbody_app; unfold fe_app.
      constructor 5 with ω b.
      { apply fs_var; rew env. }
      constructor 4.
      { apply fs_var; rew env. }
      simpl.
      apply fs_var; rew env.
    + constructor 7 with (1 := H).
      rewrite Hparam_app, Hbody_app; unfold fe_app.
      constructor 5 with ⟨t,a⟩ b.
      { apply fs_var; rew env. }
      constructor 5 with t a.
      { apply fs_var; rew env. }
      simpl.
      constructor 3.
      { apply fs_var; rew env. }
      apply IHa.
      constructor 3;
        apply fs_var; rew env.
  Qed.

  Fact fe_roll_spec f e a : f // e ~~> a -> CALL f_roll ON f // e ~~> bt_roll a.
  Proof.
    destruct a as [ | t a ]; intros H.
    + constructor 7 with (1 := H).
      rewrite Hparam_roll, Hbody_roll; unfold fe_roll.
      constructor 4.
      { apply fs_var; rew env. }
      constructor 2.
    + constructor 7 with (1 := H).
      rewrite Hparam_roll, Hbody_roll; unfold fe_roll.
      constructor 5 with t a.
      { apply fs_var; rew env. }
      apply fe_app_spec.
      constructor 3.
      { apply fs_var; rew env. }
      constructor 3.
      { apply fs_var; rew env. }
      constructor 2.
  Qed.

  Fact fe_rev_aux_spec f e a l : f // e ~~> ⟨a,l⟩ 
                              -> CALL f_rev_aux ON f // e ~~> bt_app (bt_rev l) a.
  Proof.
    revert f e a. 
    induction l as [ | b _ l IHl ]; intros f e a H.
    + constructor 7 with (1 := H).
      rewrite Hbody_rev_aux, Hparam_rev_aux; unfold fe_rev_aux.
      constructor 5 with a ω.
      * apply fs_var; rew env.
      * constructor 4.
        - apply fs_var; rew env.
        - apply fs_var.
          simpl.
          rew env.
    + constructor 7 with (1 := H).
      rewrite Hbody_rev_aux, Hparam_rev_aux; unfold fe_rev_aux.
      constructor 5 with a ⟨b,l⟩.
      * apply fs_var; rew env.
      * constructor 5 with b l.
        - apply fs_var; rew env.
        - replace (bt_app (bt_rev ⟨b,l⟩) a)
          with    (bt_app (bt_rev l) ⟨b,a⟩).
          apply IHl.
          constructor 3.
          constructor 3.
          1,2,3: apply fs_var; rew env.
          simpl.
          rewrite <- bt_app_assoc; auto.
  Qed.

  Fact fe_rev_spec f e a : f // e ~~> a -> CALL f_rev ON f // e ~~> bt_rev a.
  Proof.
    intros H.
    constructor 7 with a; auto.
    rewrite Hparam_rev, Hbody_rev; unfold fe_rev.
    rewrite <- bt_app_nil.
    apply fe_rev_aux_spec.
    constructor 3.
    * constructor 2.
    * apply fs_var; rew env.
  Qed.

(*
  Fact fe_rev_spec f e a : f // e ~~> a -> CALL f_rev ON f // e ~~> bt_rev a.
  Proof.
    revert f e; induction a as [ | t _ a IHa ]; intros f e H.
    + constructor 7 with (1 := H).
      rewrite Hparam_rev, Hbody_rev; unfold fe_rev.
      constructor 4.
      { apply fs_var; rew env. }
      constructor 2.
    + constructor 7 with (1 := H).
      rewrite Hparam_rev, Hbody_rev; unfold fe_rev.
      constructor 5 with t a.
      { apply fs_var; rew env. }
      simpl; apply fe_app_spec.
      constructor 3.
      * apply IHa.
        apply fs_var; rew env.
      * constructor 3.
        { apply fs_var; rew env. }
        constructor 2.
  Qed.
*)

End bt_list.

Local Notation "f // e ~~> v [ p , b ]" := (fun_sem p b f e v) (at level 70, format "f  //  e  ~~>  v  [ p , b ]", no associativity).

Check fe_mirror_spec.
Check fe_roll_spec.
Check fe_rev_spec.

