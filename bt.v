(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

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

Definition bt_compute_mirror s : { t | s ⋈ t }.
Proof.
  induction s as [ | a (ma & Ha) b (mb & Hb) ].
  exists ω; constructor.
  exists ⟨mb,ma⟩; constructor; auto.
Qed.

Reserved Notation "〈 t 〉" (at level 0, format "〈 t 〉", no associativity).

Fixpoint bt_size t :=
  match t with 
    | ω     => 1
    | ⟨s,t⟩ => 1 + 〈s〉 + 〈t〉
  end
where "〈 t 〉" := (bt_size t).

Fact bt_mirror_size s t : s ⋈ t -> 〈s〉 = 〈t〉.
Proof. induction 1; simpl; lia. Qed.

