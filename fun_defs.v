(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Wellfounded.

Require Import bt env.

Set Implicit Arguments.

Inductive Var : Set := in_Var : nat -> Var.
Inductive Fun : Set := in_Fun : nat -> Fun.

Hint Resolve eq_nat_dec.

Definition Var_eq_dec : forall x y : Var, { x = y } + { x <> y }.
Proof. decide equality. Qed.

Definition Fun_eq_dec : forall f g : Fun, { f = g } + { f <> g }.
Proof. decide equality. Qed.

Local Notation "e ⇢ x" := (@get_env _ _ e x).
Local Notation "e ⦃  x ⇠ v ⦄" := (@set_env _ _ Var_eq_dec e x v).

Inductive fun_expr : Set := 
  | fe_var    : Var -> fun_expr

  | fe_null   : fun_expr
  | fe_pair   : fun_expr -> fun_expr -> fun_expr
  | fe_match  : fun_expr -> fun_expr -> Var -> Var -> fun_expr -> fun_expr

  | fe_let    : Var -> fun_expr -> fun_expr -> fun_expr

  | fe_call   : Fun -> fun_expr -> fun_expr.
  
Delimit Scope expr_scope with fun_expr.

Notation " £ x " := (fe_var x) (at level 0, format "£ x") : expr_scope.

Notation ø := fe_null.
Notation " x '#' y " := (fe_pair x y) (at level 26, y at level 0, format "x # y", right associativity) : expr_scope.
Notation " 'MATCH' e 'WITH' 'ø' ⇒ a 'OR' x '#' y ⇒ b " := (fe_match e a x y b) (at level 29, format "MATCH  e  WITH  ø  ⇒  a  OR  x # y  ⇒  b", x at level 0, y at level 0) : expr_scope. 

Notation " 'LET' x '::=' y 'IN' z " := (fe_let x y z) (at level 25, format "LET  x ::= y  IN  z", x at level 0, y at level 0, z at level 0) : expr_scope.
Notation " 'CALL' f 'ON' x " := (fe_call  f x) (at level 25, f at level 0, format "CALL  f  ON  x", x at level 0) : expr_scope.

Open Scope expr_scope.

Reserved Notation " f '//' s '~~>' v" (at level 70, no associativity).

Section fun_sem.

  Variable (param : Fun -> Var) (body : Fun -> fun_expr).

  Inductive fun_sem : fun_expr -> env Var bt -> bt -> Prop := 
    | in_fs_var  : forall x e,                       £ x // e ~~> e⇢x
    | in_fs_null : forall e,                           ø // e ~~> ω
    | in_fs_pair : forall f g e a b,                   f // e ~~> a
                                               ->      g // e ~~> b
                                               ->    f#g // e ~~> ⟨a,b⟩
    | in_fs_match_0 : forall f u x y v e a,            f // e ~~> ω
                            ->                         u // e ~~> a
                            -> MATCH f WITH ø⇒u OR x#y⇒v // e ~~> a
    | in_fs_match_1 : forall f u x y v e a b c,        f // e ~~> ⟨a,b⟩
                            ->                         v // e⦃x⇠a⦄⦃y⇠b⦄ ~~> c
                            -> MATCH f WITH ø⇒u OR x#y⇒v // e ~~> c
    | in_fs_let : forall x f g e a b,                  f // e ~~> a
                            ->                         g // e⦃x⇠a⦄ ~~> b
                            ->            LET x::=f IN g // e ~~> b
    | in_fs_call : forall p g e a b,                   g // e ~~> a
                            ->                    body p // e⦃param p⇠a⦄ ~~> b
                            ->               CALL p ON g // e ~~> b

  where "f // e ~~> v" := (fun_sem f e v). 

  Fact fs_var x e a : e⇢x = a -> £x // e ~~> a.
  Proof. intros []; constructor. Qed.

  Fact fun_sem_var_inv x e a : £x // e ~~> a -> a = e⇢x.
  Proof. inversion 1; auto. Qed.

  Fact fun_sem_null_inv e a : ø // e ~~> a -> a = ω.
  Proof. inversion 1; auto. Qed.

  Fact fun_sem_pair_inv f g e v : f#g// e ~~> v -> exists a b, v = ⟨a,b⟩ /\ f // e ~~> a /\ g // e ~~> b.
  Proof. inversion 1; exists a, b; auto. Qed.
 
  Fact fun_sem_match_inv f u x y v e c :
        MATCH f WITH ø⇒u OR x#y⇒v // e ~~> c -> f // e ~~> ω /\ u // e ~~> c 
                                 \/ exists a b, f // e ~~> ⟨a,b⟩ /\ v // e⦃x⇠a⦄⦃y⇠b⦄ ~~> c.
  Proof.
    inversion 1.
    + left; auto.
    + right; exists a, b; auto.
  Qed.

  Fact fun_sem_let_inv x f g e v : LET x::=f IN g // e ~~> v -> exists a, f // e ~~> a /\ g // e⦃x⇠a⦄ ~~> v.
  Proof. inversion 1; exists a; auto. Qed.
  
  Fact fun_sem_call_inv fi g e v : CALL fi ON g // e ~~> v -> exists a, g // e ~~> a /\ body fi // e⦃param fi⇠a⦄ ~~> v.
  Proof. inversion 1; exists a; auto. Qed.

  Fact fun_sem_det f e a b : f // e ~~> a -> f // e ~~> b -> a = b.
  Proof.
    intros H1; revert H1 b.
    induction 1 as [ x e 
                   | e 
                   | f g e a b H1 IH1 H2 IH2 
                   | f u x y v e a H1 IH1 H2 IH2 
                   | f u x y v e a b c H1 IH1 H2 IH2 
                   | x f g e a b H1 IH1 H2 IH2 
                   | p g e a b H1 IH1 H2 IH2 ].
    + intros v H; apply fun_sem_var_inv in H; auto.
    + intros v H; apply fun_sem_null_inv in H; auto.
    + intros v H; apply fun_sem_pair_inv in H.
      destruct H as (a' & b' & H3 & H4 & H5); subst; f_equal; auto.
    + intros c H.
      apply fun_sem_match_inv in H.
      destruct H as [ (H3 & H4) | (a' & b' & H3 & H4) ]; auto.
      apply IH1 in H3; discriminate.
    + intros w H.
      apply fun_sem_match_inv in H.
      destruct H as [ (H3 & H4) | (a' & b' & H3 & H4) ].
      * apply IH1 in H3; discriminate.
      * apply IH1 in H3; inversion H3.
        apply IH2; subst; auto.
    + intros v H.
      apply fun_sem_let_inv in H.
      destruct H as (a' & H3 & H4).
      apply IH1 in H3; subst; auto.
    + intros v H.
      apply fun_sem_call_inv in H.
      destruct H as (a' & H3 & H4).
      apply IH1 in H3; subst; auto.
  Qed.

  Section loop.

    Variables (p : Var) (loop : Fun) (Hloop1 : param loop = p) (Hloop2 : body loop = CALL loop ON £p).

    Let loop_does_not_stop f e a : f // e ~~> a -> forall e', f = CALL loop ON e' -> False.
    Proof.
      induction 1 as [ x e 
                     | e 
                     | f g e a b H1 IH1 H2 IH2 
                     | f u x y v e a H1 IH1 H2 IH2 
                     | f u x y v e a b c H1 IH1 H2 IH2 
                     | x f g e a b H1 IH1 H2 IH2 
                     | fi g e a b H1 IH1 H2 IH2 ]; intros e'; try discriminate.
      inversion 1; subst fi g.
      rewrite Hloop2 in IH2.
      apply (IH2 _ eq_refl).
    Qed.
 
    Theorem loop_spec f e a : ~ CALL loop ON f // e ~~> a.
    Proof.
      intros H.
      apply loop_does_not_stop with (1 := H) (2 := eq_refl).
    Qed.

  End loop.

End fun_sem.
