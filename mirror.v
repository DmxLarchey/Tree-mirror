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

  Variables (u x y z : Var) (Hxy : x <> y).
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

End mirror.

Section bt_list.

  Variables (u x y z : Var) (Hxy : x <> y) (Hux : u <> x) (Huy : u <> y).
  Variable (f_app f_roll f_rev : Fun).

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

  Definition fe_rev := 
    MATCH £u WITH 
         ø⇒ø 
    OR x#y⇒CALL f_app ON (CALL f_rev ON £y#(£x#ø)).

  Variable (param : Fun -> Var)     
           (body : Fun -> fun_expr) 
           (Hparam_app : param f_app = u) (Hbody_app : body f_app = fe_app)
           (Hparam_roll : param f_roll = u) (Hbody_roll : body f_roll = fe_roll)
           (Hparam_rev : param f_rev = u) (Hbody_rev : body f_rev = fe_rev).

  Notation "f // s ~~> v" := (fun_sem param body f s v).

  Fact fe_app_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL f_app ON f // e ~~> bt_app a b.
  Proof.
    revert f e; induction a as [ | t _ a IHa ]; intros f e H.
    + constructor 7 with (1 := H).
      rewrite Hparam_app, Hbody_app; unfold fe_app.
      constructor 5 with ω b.
      { apply fs_var; rew env. }
      constructor 4.
      { apply fs_var; rew env. }
      apply fs_var; rew env.
    + constructor 7 with (1 := H).
      rewrite Hparam_app, Hbody_app; unfold fe_app.
      constructor 5 with ⟨t,a⟩ b.
      { apply fs_var; rew env. }
      constructor 5 with t a.
      { apply fs_var; rew env. }
      simpl; constructor 3.
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

End bt_list.

Local Notation "f // e ~~> v [ p , b ]" := (fun_sem p b f e v) (at level 70, format "f  //  e  ~~>  v  [ p , b ]", no associativity).

Check fe_mirror_spec.
Check fe_roll_spec.
Check fe_rev_spec.

