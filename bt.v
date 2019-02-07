(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Wf.

Set Implicit Arguments.

(** Binary trees *)

Inductive bt : Set := bt0 | bt1 : bt -> bt -> bt.

Delimit Scope bt_scope with bt.

Notation ω := bt0.
Notation " ⟨ x , y ⟩ " := (bt1 x y) (at level 0, format "⟨ x , y ⟩"): bt_scope.

Reserved Notation " '[[' t ']]' " (at level 0, no associativity).

Open Scope bt_scope.

(* We can decide if two trees are equal or not *)

Definition bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
Proof.
  revert t; induction s as [ | a Ha b Hb ]; intros [ | c d ].
  left; auto.
  right; discriminate.
  right; discriminate.
  destruct (Ha c) as [ E1 | E1 ].
  destruct (Hb d) as [ E2 | E2 ].
  subst; left; auto.
  right; contradict E2; inversion E2; auto.
  right; contradict E1; inversion E1; auto.
Qed.

Fact bt_pair_neq a1 b1 a2 b2 : ⟨a1,a2⟩ <> ⟨b1,b2⟩ -> { a1 <> b1 } + { a2 <> b2 }.
Proof. 
  intros H.
  destruct (bt_eq_dec a1 b1); auto.
  destruct (bt_eq_dec a2 b2); auto.
  subst; destruct H; auto.
Qed.

Reserved Notation "x ⋈ y" (at level 70, no associativity, format "x  ⋈  y").

Inductive bt_mirror : bt -> bt -> Prop :=
  | in_bt_mirror_0 : ω ⋈ ω
  | in_bt_mirror_1 : forall a b c d, a ⋈ b -> c ⋈ d -> ⟨a,c⟩ ⋈ ⟨d,b⟩
where "x ⋈ y" := (bt_mirror x y).

Fixpoint btm t :=
  match t with
    | ω     => ω
    | ⟨u,v⟩ => ⟨btm v,btm u⟩
  end.

Definition btm_spec s : s ⋈ btm s.
Proof. induction s; constructor; auto. Qed.

Reserved Notation "〈 t 〉" (at level 0, format "〈 t 〉", no associativity).

Fixpoint bts t :=
  match t with 
    | ω     => 1
    | ⟨s,t⟩ => 1 + 〈s〉 + 〈t〉
  end
where "〈 t 〉" := (bts t).

Fact bt_mirror_size s t : s ⋈ t -> 〈s〉 = 〈t〉.
Proof. induction 1; simpl; lia. Qed.

Reserved Notation " ⟦ x ⟧ " (at level 0). 

Fixpoint bt_nat t :=
  match t with 
    | ω     => 0
    | ⟨_,t⟩ => 1 + bt_nat t
  end.

Fixpoint nat_bt n := 
  match n with
    | 0   => ω
    | S n => ⟨ω,⟦n⟧⟩
  end
where "⟦ x ⟧" := (nat_bt x).

Fact nat_bt_nat n : bt_nat ⟦n⟧ = n.
Proof.
  induction n; simpl; f_equal; auto.
Qed.

Fixpoint bt_add u v :=
  match u with 
    | ω     => v
    | ⟨_,u⟩ => ⟨ω,bt_add u v⟩
  end.

Fact bt_add_spec m n : bt_add ⟦n⟧ ⟦m⟧ = ⟦n+m⟧.
Proof. induction n; simpl; f_equal; auto. Qed.

Fixpoint bt_mul u v := 
  match u with 
    | ω     => ω
    | ⟨_,u⟩ => bt_add v (bt_mul u v)
  end.

Fact bt_mul_spec m n : bt_mul ⟦n⟧ ⟦m⟧ = ⟦n*m⟧.
Proof. 
  induction n; simpl; f_equal; auto.
  rewrite IHn, bt_add_spec; trivial.
Qed.

Fixpoint fact n :=
  match n with
    | 0 => 1
    | S n => S n * fact n
  end.

Fixpoint bt_fact u :=
  match u with
    | ω     => ⟨ω,ω⟩
    | ⟨_,v⟩ => bt_mul u (bt_fact v)
  end.

Fact bt_fact_0 : bt_fact ⟦0⟧ = ⟦1⟧.
Proof. auto. Qed.

Fact bt_fact_S n : bt_fact ⟦S n⟧ = bt_mul ⟦S n⟧ (bt_fact ⟦n⟧).
Proof. auto. Qed.

Fact bt_fact_spec n : bt_fact ⟦n⟧ = ⟦fact n⟧.
Proof.
  induction n as [ | n IHn ].
  + rewrite bt_fact_0; auto.
  + rewrite bt_fact_S, IHn, bt_mul_spec; auto.
Qed.

Definition bt_bool t :=
  match t with
    | ω => false
    | _ => true
  end.

Definition bool_bt (b : bool) := if b then ⟨ω,ω⟩ else ω.

Fact bt_bool_bt b : bt_bool (bool_bt b) = b.
Proof. destruct b; auto. Qed.

Fixpoint bt_nat_le a b :=
  match a, b with
    | ω, _         => ⟨ω,ω⟩ 
    | _, ω         => ω
    | ⟨_,a⟩, ⟨_,b⟩ => bt_nat_le a b
  end.

Fact bt_nat_le_spec n m : bt_nat_le ⟦n⟧ ⟦m⟧ = bool_bt (leb n m).
Proof.
  revert m; induction n as [ | n IHn ]; [ intros m | intros [ | ] ]; simpl; auto.
Qed.

Fixpoint bt_size t :=
  match t with 
    | ω     => ⟨ω,ω⟩
    | ⟨u,v⟩ => ⟨ω,bt_add (bt_size u) (bt_size v)⟩
  end.

Fact bt_size_spec t : bt_size t = ⟦〈t〉⟧.
Proof.
  induction t as [ | u Hu v Hv ]; simpl; f_equal; auto.
  rewrite Hu, Hv, bt_add_spec; trivial.
Qed.

Fixpoint bt_app t a :=
  match t with
    | ω     => a
    | ⟨u,v⟩ => ⟨u,bt_app v a⟩
  end.

Definition bt_roll t :=
  match t with
    | ω     => ω 
    | ⟨a,b⟩ => bt_app b ⟨a,ω⟩
  end.

Fixpoint bt_list t :=
  match t with
    | ω     => nil
    | ⟨u,v⟩ => u::bt_list v
  end.

Fixpoint list_bt l :=
  match l with
    | nil  => ω
    | u::l => ⟨u,list_bt l⟩
  end.

Fact list_bt_cons a l : list_bt (a::l) = ⟨a,list_bt l⟩.
Proof. trivial. Qed.

Fact bt_list_bt l : bt_list (list_bt l) = l.
Proof. induction l; simpl; f_equal; auto. Qed.

Fact list_bt_list t : list_bt (bt_list t) = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Fact bt_app_list l m : bt_app (list_bt l) (list_bt m) = list_bt (l++m).
Proof. induction l; simpl; f_equal; auto. Qed.

Fact bt_roll_list a l : bt_roll (list_bt (a::l)) = list_bt (l++a::nil).
Proof.
  unfold bt_roll; simpl.
  rewrite <- bt_app_list; auto.
Qed.

Fixpoint bt_rev t :=
  match t with
    | ω     => ω
    | ⟨a,b⟩ => bt_app (bt_rev b) ⟨a,ω⟩
  end.

Fact bt_rev_list l : bt_rev (list_bt l) = list_bt (rev l).
Proof.
  induction l; simpl; auto.
  rewrite <- bt_app_list; f_equal; auto.
Qed.


(* A positive binary number is a list 0..1....0 ending with a 1 *)

Fixpoint bt_pos t :=
  match t with
    | ω     => 1
    | ⟨ω,t⟩ => 2*bt_pos t
    | ⟨_,t⟩ => 1+2*bt_pos t
  end.

Fixpoint div_mod_2 n : { q : nat & { b | n = b + 2*q /\ b < 2 } }.
Proof.
  destruct n as [ | [ | n ] ].
  + exists 0, 0; simpl; lia.
  + exists 0, 1; simpl; lia.
  + destruct (div_mod_2 n) as (q & b & H1 & H2).
    exists (S q), b; subst; simpl; lia.
Qed.

Definition pos_bt_full n : { t | bt_pos t = S n }.
Proof.
  induction n as [ n IHn ] using (well_founded_induction_type lt_wf).
  destruct (div_mod_2 (S n)) as ([ | q ] & b & H1 & H2).
  + destruct b as [ | [ | ] ].
    - discriminate.
    - exists ω; simpl; lia.
    - exfalso; lia.
  + destruct (IHn q) as (t & Ht); try lia.
    destruct b as [ | b ].
    - exists ⟨ω,t⟩; simpl; lia.
    - exists ⟨⟨ω,ω⟩,t⟩; simpl; lia.
Qed.

Definition pos_bt n := 
  match n with 0 => ω | S n => proj1_sig (pos_bt_full n) end.

Fact pos_bt_spec n : bt_pos (pos_bt (S n)) = S n.
Proof. apply (proj2_sig (pos_bt_full n)). Qed.

Definition bt_add3 r s t :=
  match r, s, t with
    | ω,   ω,   ω   => ( ω, ω ) 
    | _,   ω,   ω   => ( ω, ⟨ω,ω⟩ )
    | ω,   _,   ω   => ( ω, ⟨ω,ω⟩ )
    | _,   _,   ω   => ( ⟨ω,ω⟩, ω )
    | ω,   ω,   _   => ( ω, ⟨ω,ω⟩ )
    | _,   ω,   _   => ( ⟨ω,ω⟩, ω )
    | ω,   _,   _   => ( ⟨ω,ω⟩, ω )
    | _,   _,   _   => ( ⟨ω,ω⟩, ⟨ω,ω⟩ )
  end.

Fixpoint bt_pos_succ t :=
  match t with
    | ω     => ⟨ω,ω⟩
    | ⟨ω,t⟩ => ⟨⟨ω,ω⟩,t⟩
    | ⟨_,t⟩ => ⟨ω,bt_pos_succ t⟩
  end.

Fact bt_pos_succ_spec t : bt_pos (bt_pos_succ t) = S (bt_pos t).
Proof.
  induction t as [ | [|] _ t IHt ]; auto.
  simpl; rewrite IHt; lia.
Qed.

Definition bt_pos_add_digit d t :=
  match d with
    | ω => t
    | _ => bt_pos_succ t
  end.



