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

Section arith.

  Variables (u x y z : Var) (Hxy : x <> y) (Hxz : x <> z) (Hyz : y <> z) (Hux : u <> x).

  Variable (p_add p_mul p_fact p_size 
            p_leb 
            : Fun).

  Definition fe_add := 
    MATCH £u WITH
         ø   ⇒ ø 
      OR x#z ⇒ 
      MATCH £x WITH
           ø   ⇒ £z 
        OR x#y ⇒ ø#CALL p_add ON (£y#£z).

  Definition fe_mul :=
    MATCH £u WITH
         ø   ⇒ ø 
      OR x#z ⇒ 
      MATCH £x WITH
           ø   ⇒ ø
        OR x#y ⇒ CALL p_add ON (£z#CALL p_mul ON (£y#£z)).

  Definition fe_fact :=
    MATCH £u WITH
         ø   ⇒ ø#ø 
      OR x#x ⇒ CALL p_mul ON (£u#CALL p_fact ON £x). 

  Definition fe_leb :=
    MATCH £u WITH
         ø   ⇒ ø 
      OR u#x ⇒ 
      MATCH £u WITH
           ø   ⇒ ø#ø 
        OR u#u ⇒ 
        MATCH £x WITH
           ø   ⇒ ø 
        OR x#x ⇒ CALL p_leb ON (£u#£x).

  Definition fe_size :=
    MATCH £u WITH
         ø   ⇒ ø#ø
      OR x#y ⇒ ø#CALL p_add ON (CALL p_size ON £x#CALL p_size ON £y).

  Variable (param : Fun -> Var)     
           (body : Fun -> fun_expr) 
           
           (Hparam_add : param p_add = u)    
           (Hparam_mul : param p_mul = u)
           (Hparam_fact : param p_fact = u)
           (Hparam_leb : param p_leb = u)
           (Hparam_size : param p_size = u) 

           (Hbody_add : body p_add = fe_add) 
           (Hbody_mul : body p_mul = fe_mul)
           (Hbody_fact : body p_fact = fe_fact)
           (Hbody_leb : body p_leb = fe_leb)
           (Hbody_size : body p_size = fe_size).

  Notation "f // s ~~> v" := (fun_sem param body f s v).

  Fact fe_add_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL p_add ON f // e ~~> bt_add a b.
  Proof.
    revert f e; induction a as [ | a1 IH1 a2 IH2 ]; intros f e H3; simpl; 
      constructor 7 with (1 := H3); rewrite Hbody_add, Hparam_add; unfold fe_add.
    + constructor 5 with ω b.
      1: apply fs_var; rew env.
      constructor 4; apply fs_var; rew env.
    + constructor 5 with ⟨a1,a2⟩ b.
      1: apply fs_var; rew env.
      constructor 5 with a1 a2.
      1: apply fs_var; rew env.
      constructor 3.
      1: constructor 2.
      apply IH2.
      constructor 3; apply fs_var; rew env.
  Qed.

  Fact fe_mul_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL p_mul ON f // e ~~> bt_mul a b.
  Proof.
    revert f e; induction a as [ | a1 IH1 a2 IH2 ]; intros f e H3; simpl; 
      constructor 7 with (1 := H3); rewrite Hbody_mul, Hparam_mul; unfold fe_mul.
    + constructor 5 with ω b.
      1: apply fs_var; rew env.
      constructor 4. 
      * apply fs_var; rew env.
      * constructor 2.
    + constructor 5 with ⟨a1,a2⟩ b.
      1: apply fs_var; rew env.
      constructor 5 with a1 a2.
      1: apply fs_var; rew env.
      apply fe_add_spec.
      constructor 3.
      1: apply fs_var; rew env.
      apply IH2.
      constructor 3; apply fs_var; rew env.
  Qed.

  Fact fe_fact_spec f e a : f // e ~~> a -> CALL p_fact ON f // e ~~> bt_fact a.
  Proof.
    revert f e; induction a as [ | v _ a IHa ]; intros f e H;
      constructor 7 with (1 := H); rewrite Hbody_fact, Hparam_fact; unfold fe_fact.
    + constructor 4.
      1: apply fs_var; rew env.
      constructor 3; constructor 2.
    + constructor 5 with v a.
      1: apply fs_var; rew env.
      apply fe_mul_spec; fold bt_fact.
      constructor 3.
      * apply fs_var; rew env.
      * apply IHa, fs_var; rew env.
  Qed.

  Fact fe_leb_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL p_leb ON f // e ~~> bt_nat_le a b.
  Proof.
    revert f e b; induction a as [ | p _ a IHa ]; intros f e b H; 
      constructor 7 with (1 := H); rewrite Hbody_leb, Hparam_leb; unfold fe_leb.
    + constructor 5 with ω b.
      1: apply fs_var; rew env.
      constructor 4.
      1: apply fs_var; rew env.
      constructor 3; constructor 2.
    + constructor 5 with ⟨p,a⟩ b.
      1: apply fs_var; rew env.
      constructor 5 with p a.
      1: apply fs_var; rew env.
      destruct b as [ | q b ].
      * constructor 4.
        1: apply fs_var; rew env.
        constructor 2.
      * constructor 5 with q b.
        1: apply fs_var; rew env.
        apply IHa.
        constructor 3; apply fs_var; rew env.
  Qed.

  Fact fe_size_spec f e t : f // e ~~> t -> CALL p_size ON f // e ~~> bt_size t.
  Proof.
    revert f e; induction t as [ | a IHa b IHb ]; intros f e H; simpl;
      constructor 7 with (1 := H); rewrite Hbody_size, Hparam_size; unfold fe_size.
    + constructor 4.
      1: apply fs_var; rew env.
      constructor 3; constructor 2.
    + constructor 5 with a b.
      1: apply fs_var; rew env.
      constructor 3.
      1: constructor 2.
      apply fe_add_spec.
      constructor 3.
      * apply IHa, fs_var; rew env.
      * apply IHb, fs_var; rew env.
  Qed.

End arith.

Local Notation "f // e ~~> v [ p , b ]" := (fun_sem p b f e v) (at level 70, format "f  //  e  ~~>  v  [ p , b ]", no associativity).

Check fe_add_spec.
Check fe_mul_spec.
Check fe_size_spec.

