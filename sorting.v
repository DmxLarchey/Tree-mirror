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

Section measure_rect.

  Variables (X : Type) (m : X -> nat) (P : X -> Type)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Theorem measure_rect : forall x, P x.
  Proof.
    apply (@well_founded_induction_type _ (fun x y => m x < m y)); auto.
    apply wf_inverse_image, lt_wf.
  Qed.

End measure_rect.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  induction x as [ x IH ] using (@measure_rect _ (fun x => f)). 

Section measure_rect2.

  Variables (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type)
            (HP : forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Let Q (c : X*Y) := P (fst c) (snd c).

  Theorem measure_rect2 : forall x y, P x y.
  Proof.
    intros x y.
    change (Q (x,y)).
    generalize (x,y); clear x y; intros c.
    induction on c as IHc with measure (m (fst c) (snd c)).
    destruct c as (x,y); simpl in *.
    apply HP.
    intros x' y'; simpl; apply (IHc (x',y')).
  Qed. 

End measure_rect2.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  revert x y; apply measure_rect2 with (m := fun x y => f); intros x y IH.

Section sorting.

  Variables (u x y z : Var) (Hxy : x <> y) (Hxz : x <> z) (Hyz : y <> z) (Hux : u <> x) (Huy : u <> y) (Huz : u <> z).

  Variable (p_split p_merge p_merge_sort p_cmp p_leq : Fun).

  Variable (param : Fun -> Var)     
           (body : Fun -> fun_expr).

  Notation "f // s ~~> v" := (fun_sem param body f s v).

  Definition fe_cmp := 
    MATCH £u WITH
        ø   ⇒ ø 
     OR x#y ⇒ MATCH £x WITH
          ø   ⇒ MATCH £y WITH
            ø   ⇒ ø
         OR x#x ⇒ ø#ø
       OR u#x ⇒ MATCH £y WITH
            ø   ⇒ ø#(ø#ø)
         OR z#y ⇒ MATCH CALL p_cmp ON (£u#£z) WITH
              ø   ⇒ CALL p_cmp ON (£x#£y)
           OR u#x ⇒ £u#£x.

  Hypothesis (Hparam_cmp : param p_cmp = u) (Hbody_cmp : body p_cmp = fe_cmp).

  Fact fe_cmp_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL p_cmp ON f // e ~~> bt_compare a b.
  Proof.
    revert b e f; induction a as [ | a1 H1 a2 H2 ]; intros [ | b1 b2 ] e f H;
      constructor 7 with (1 := H); rewrite Hbody_cmp, Hparam_cmp; unfold fe_cmp.
    + constructor 5 with ω ω.
      1: apply fs_var; rew env.
      constructor 4.
      1: apply fs_var; rew env.
      constructor 4.
      1: apply fs_var; rew env.
      constructor 2.
    + constructor 5 with ω ⟨b1,b2⟩.
      1: apply fs_var; rew env.
      constructor 4.
      1: apply fs_var; rew env.
      constructor 5 with b1 b2.
      1: apply fs_var; rew env.
      constructor 3; constructor 2.
    + constructor 5 with ⟨a1,a2⟩ ω.
      1: apply fs_var; rew env.
      constructor 5 with a1 a2.
      1: apply fs_var; rew env.
      constructor 4.
      1: apply fs_var; rew env.
      repeat constructor 3; constructor 2.
    + constructor 5 with ⟨a1,a2⟩ ⟨b1,b2⟩.
      1: apply fs_var; rew env.
      constructor 5 with a1 a2.
      1: apply fs_var; rew env.
      constructor 5 with b1 b2.
      1: apply fs_var; rew env.
      match goal with |- _ // ?e ~~> _ => set (e' := e) end. 
      specialize (H1 b1 e' (£u#£z)).
      simpl.
      destruct (bt_compare a1 b1) as [ | x1 x2 ].
      * constructor 4.
        1: apply H1; unfold e'; constructor 3; apply fs_var; rew env.
        apply H2; constructor 3; unfold e'; apply fs_var; rew env.
      * constructor 5 with x1 x2.
        1:apply H1; unfold e'; constructor 3; apply fs_var; rew env.
        constructor 3; apply fs_var; rew env.
  Qed.

  Definition fe_leq :=
    MATCH CALL p_cmp ON £u WITH
        ø   ⇒ ø#ø
     OR x#x ⇒ MATCH £x WITH
          ø   ⇒ ø#ø
       OR x#x ⇒ ø.

  Hypothesis (Hparam_leq : param p_leq = u) (Hbody_leq : body p_leq = fe_leq).

  Fact fe_leq_spec f e a b : f // e ~~> ⟨a,b⟩ -> CALL p_leq ON f // e ~~> bt_leq a b.
  Proof.
    intros H.
    constructor 7 with (1 := H); rewrite Hbody_leq, Hparam_leq; unfold fe_leq.
    generalize (@fe_cmp_spec £u (e⦃u⇠⟨a,b⟩⦄) a b) (bt_compare_3 a b).
    unfold bt_leq. 
    intros H1 [ H2 | [ H2 | H2 ] ].
    + constructor 4.
      * rewrite <- H2; apply H1, fs_var; rew env.
      * rewrite H2; constructor 3; constructor 2.
    + constructor 5 with ω ω.
      * rewrite <- H2; apply H1, fs_var; rew env.
      * constructor 4.
        1: apply fs_var; rew env.
        rewrite H2; constructor 3; constructor 2.
    + constructor 5 with ω ⟨ω,ω⟩.
      * rewrite <- H2.
        apply fe_cmp_spec, fs_var; rew env.
      * rewrite H2.
        constructor 5 with ω ω.
        1: apply fs_var; rew env.
        constructor 2.
  Qed.

  Definition fe_split :=
    MATCH £u WITH
        ø   ⇒ ø#ø
     OR x#u ⇒ MATCH £u WITH
          ø   ⇒ (£x#ø)#ø
       OR y#u ⇒ MATCH CALL p_split ON £u WITH
            ø   ⇒ ø#ø
         OR u#z ⇒ (£x#£u)#(£y#£z).

  Hypothesis (Hparam_split : param p_split = u) (Hbody_split : body p_split = fe_split).

  Fact fe_split_spec f e l : f // e ~~> l -> CALL p_split ON f // e ~~> bt_split l.
  Proof.
    revert f e.
    induction on l as IHl with measure (bt_length l); intros f e H.
    constructor 7 with (1 := H); rewrite Hbody_split, Hparam_split; unfold fe_split.
    destruct l as [ | t1 [ | t2 l ] ].
    + constructor 4.
      1: apply fs_var; rew env.
      simpl; constructor 3; constructor 2.
    + constructor 5 with t1 ω.
      1: apply fs_var; rew env.
      simpl; constructor 4.
      1: apply fs_var; rew env.
      repeat constructor 3; try constructor 2.
      apply fs_var; rew env.
    + constructor 5 with t1 ⟨t2,l⟩.
      1: apply fs_var; rew env.
      constructor 5 with t2 l.
      1: apply fs_var; rew env.
      specialize (IHl l); simpl.
      destruct (bt_split l) as [ | l1 l2 ].
      * constructor 4. 
        - apply IHl; simpl; try lia.
          apply fs_var; rew env.
        - constructor 3; constructor 2.
      * constructor 5 with l1 l2.
        - apply IHl; simpl; try lia.
          apply fs_var; rew env.
        - constructor 3; constructor 3; apply fs_var; rew env.
  Qed.

(*
  Fixpoint bt_merge_rec n l m :=
  match n with 
    | 0   => ω
    | S n => match l, m with 
               | ω    , _       => m
               | _    , ω       => l
               | ⟨r,l'⟩, ⟨s,m'⟩ => match bt_leq r s with 
                                     | ω => ⟨s,bt_merge_rec n l m'⟩
                                     | _ => ⟨r,bt_merge_rec n l' m⟩
                                   end
             end
  end.

*)

  Variable (v x1 y1 : Var).

  Definition fe_merge :=
     MATCH £u WITH
        ø   ⇒ ø
     OR u#v ⇒ MATCH £u WITH
          ø    ⇒ £v
       OR x#x1 ⇒ MATCH £v WITH
            ø    ⇒ £u
         OR y#y1 ⇒ MATCH CALL p_leq ON (£x#£y) WITH
                ø   ⇒ £y#CALL p_merge ON (£u#£y1)
             OR u#u ⇒ £x#CALL p_merge ON (£x1#£v).

  Hypothesis (Hparam_merge : param p_merge = u) (Hbody_merg : body p_merge = fe_merge).

  Fact fe_merge_spec f e l m : f // e ~~> ⟨l,m⟩ -> CALL p_merge ON f // e ~~> bt_merge l m.
  Proof.
    revert l m.
    Check measure_rect2.
    apply measure_rect2 with (m := fun l m => bt_length l+bt_length m).
 induction on l m as IH with measure (bt_length l+bt_length m).


   
    



         OR x#x ⇒ ø#ø
       OR u#x ⇒ MATCH £y WITH
            ø   ⇒ ø#(ø#ø)


           (Hparam_mul : param p_mul = u)
           (Hparam_fact : param p_fact = u)
           (Hparam_leb : param p_leb = u)
           (Hparam_size : param p_size = u) 

           (Hbody_add : body p_add = fe_add) 
           (Hbody_mul : body p_mul = fe_mul)
           (Hbody_fact : body p_fact = fe_fact)
           (Hbody_leb : body p_leb = fe_leb)
           (Hbody_size : body p_size = fe_size).


  Fact f_cmp

  Definition fe_add := 
    MATCH £u WITH
         ø   ⇒ ø 
      OR x#z ⇒ 
      MATCH £x WITH
           ø   ⇒ £z 
        OR x#y ⇒ ø#CALL p_add ON (£y#£z).

