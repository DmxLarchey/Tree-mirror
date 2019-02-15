(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Wellfounded Permutation Extraction.

Set Implicit Arguments.

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

  Variables (X Y : Type) (mes : X -> Y -> nat) (P : X -> Y -> Type)
            (HP : forall x y, (forall x' y', mes x' y' < mes x y -> P x' y') -> P x y).

  Let Q (c : X*Y) := P (fst c) (snd c).

  Theorem measure_rect2 : forall x y, P x y.
  Proof.
    intros x y.
    change (Q (x,y)).
    generalize (x,y); clear x y; intros c.
    induction on c as IHc with measure (mes (fst c) (snd c)).
    destruct c as (x,y); simpl in *.
    apply HP.
    intros x' y'; simpl; apply (IHc (x',y')).
  Qed. 

End measure_rect2.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x, y; revert x y; apply (@measure_rect2 _ _ (fun x y => f)); intros x y IH.

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

(* Comparison of binary trees 

   bt_compare a b returns ω if a = b
   bt_compare a b returns <ω,ω> if a < b
   bt_compare a b returns <ω,<ω,ω>> if a > b

*)

Fixpoint bt_compare a b :=
  match a, b with
    | ω       , ω       => ω
    | ω       , _       => ⟨ω,ω⟩
    | ⟨_,_⟩   , ω       => ⟨ω,⟨ω,ω⟩⟩
    | ⟨a1,a2⟩ , ⟨b1,b2⟩ => 
      match bt_compare a1 b1 with
        | ω => bt_compare a2 b2
        | x => x
      end
  end.

Fact bt_compare_3 a b : bt_compare a b = ω \/ bt_compare a b = ⟨ω,ω⟩ \/ bt_compare a b = ⟨ω,⟨ω,ω⟩⟩.
Proof.
  revert b; induction a as [ | a1 H1 a2 H2 ]; intros [ | b1 b2 ]; simpl; auto.
  destruct (H1 b1) as [ E | [ E | E ] ]; rewrite E; auto.
Qed.

Fact bt_compare_eq a b : bt_compare a b = ω <-> a = b.
Proof.
  revert b; induction a as [ | a1 H1 a2 H2 ]; intros [ | b1 b2 ]; simpl; try tauto;
    try (split; discriminate).
  specialize (H1 b1); specialize (H2 b2).
  split.
  + destruct (bt_compare a1 b1); try discriminate.
    rewrite H2, (proj1 H1); intros; subst; auto.
  + inversion 1; subst.
    rewrite (proj2 H1); tauto.
Qed.

Definition bt_3_opp a :=
  match a with
    | ω => ω 
    | ⟨ω,ω⟩ => ⟨ω,⟨ω,ω⟩⟩
    | _     => ⟨ω,ω⟩
  end.

Fact bt_compare_opp a b : bt_compare b a = bt_3_opp (bt_compare a b).
Proof.
  revert a; induction b as [ | b1 H1 b2 H2 ]; intros [ | a1 a2 ]; simpl; auto.
  rewrite H1, H2.
  destruct (bt_compare a1 b1) as [ | [ | [|] ] ]; simpl; auto.
  destruct (bt_compare a2 b2) as [ | [ | [|] ] ]; simpl; auto.
  all: destruct b3; auto.
Qed.

Definition bt_leq a b :=
  match bt_compare a b with
    | ω     => ⟨ω,ω⟩
    | ⟨ω,ω⟩ => ⟨ω,ω⟩
    | _     => ω 
  end.

Fixpoint bt_split l :=
  match l with
    | ω           => ⟨ω,ω⟩
    | ⟨t,ω⟩       => ⟨⟨t,ω⟩,ω⟩
    | ⟨t1,⟨t2,l⟩⟩ => 
    match bt_split l with
      | ω         => ⟨ω,ω⟩
      | ⟨l1,l2⟩   => ⟨⟨t1,l1⟩,⟨t2,l2⟩⟩
    end
  end.

Infix "~p" := (@Permutation _) (at level 70, no associativity).

Fixpoint bt_split_spec l : exists l1 l2, l ~p l1 ++ l2 /\ bt_split (list_bt l) = ⟨list_bt l1,list_bt l2⟩.
Proof.
  destruct l as [ | t1 [ | t2 l ] ].
  + exists nil, nil; simpl; auto.
  + exists (t1::nil), nil; simpl; auto.
  + destruct (bt_split_spec l) as (l1 & l2 & H1 & H2).
    exists (t1::l1), (t2::l2); split.
    * simpl; constructor 2.
      apply Permutation_cons_app; auto.
    * simpl; rewrite H2; auto.
Qed.

Fixpoint bt_length l :=
  match l with
    | ω     => 0
    | ⟨_,l⟩ => S (bt_length l)
  end.

Fixpoint bt_split_length l : 
   match bt_split l with
     | ω       => False
     | ⟨l1,l2⟩ => bt_length l1 + bt_length l2 = bt_length l
               /\ bt_length l2 <= bt_length l1 <= 1+bt_length l2
   end.
Proof.
  destruct l as [ | t1 [ | t2 l ] ]; simpl; auto.
  specialize (bt_split_length l).
  destruct (bt_split l) as [ | l1 l2 ]; simpl; try tauto; lia.
Qed.

Reserved Notation "x ⊕ y ⊳ z" (at level 70, no associativity).

Inductive bt_merge_graph : bt -> bt -> bt -> Prop :=
  | in_btmg_0 : forall m, ω ⊕ m ⊳ m
  | in_btmg_1 : forall l, l ⊕ ω ⊳ l
  | in_btmg_2 : forall r s l m p, bt_leq r s = ω  -> ⟨r,l⟩ ⊕ m ⊳ p -> ⟨r,l⟩ ⊕ ⟨s,m⟩ ⊳ ⟨s,p⟩
  | in_btmg_3 : forall r s l m p, bt_leq r s <> ω -> l ⊕ ⟨s,m⟩ ⊳ p -> ⟨r,l⟩ ⊕ ⟨s,m⟩ ⊳ ⟨r,p⟩
where "x ⊕ y ⊳ z" := (bt_merge_graph x y z).

Fact bt_merge_graph_fun l m p1 p2 : l ⊕ m ⊳ p1 -> l ⊕ m ⊳ p2 -> p1 = p2.
Proof.
  intros H; revert H p2.
  induction 1; inversion 1; subst; auto.
  + f_equal; auto.
  + rewrite H in H7; destruct H7; auto.
  + rewrite H7 in H; destruct H; auto.
  + f_equal; auto.
Qed.

Definition bt_merge_full l m : { p | l ⊕ m ⊳ p }.
Proof.
  induction on l m as IH with measure (bt_length l+bt_length m).
  case_eq l.
  1: exists m; subst; constructor.
  intros r l' El.
  case_eq m.
  1: exists l; subst; constructor.
  intros s m' Em.
  case_eq (bt_leq r s).
  * intros E.
    destruct (IH l m') as (p & Hp).
    + subst; simpl; lia.
    + exists ⟨s,p⟩; constructor 3; subst; auto.
  * intros u v E.
    destruct (IH l' m) as (p & Hp).
    + subst; simpl; lia.
    + exists ⟨r,p⟩; constructor 4; subst; auto.
      rewrite E; discriminate.
Qed.

Definition bt_merge l m := proj1_sig (bt_merge_full l m).

Fact bt_merge_spec l m : l ⊕ m ⊳ bt_merge l m.
Proof. apply (proj2_sig _). Qed.

Fact bt_merge_spec_1 m : bt_merge ω m = m.
Proof.
  apply bt_merge_graph_fun with (1 := bt_merge_spec _ _).
  constructor.
Qed.

Fact bt_merge_spec_2 l : bt_merge l ω = l.
Proof.
  apply bt_merge_graph_fun with (1 := bt_merge_spec _ _).
  constructor.
Qed.

Fact bt_merge_spec_3 r s l m : bt_leq r s = ω -> bt_merge ⟨r,l⟩ ⟨s,m⟩ = ⟨s,bt_merge ⟨r,l⟩ m⟩.
Proof.
  intros E.
  apply bt_merge_graph_fun with (1 := bt_merge_spec _ _).
  constructor; auto.
  apply bt_merge_spec.
Qed.

Fact bt_merge_spec_4 r s l m : bt_leq r s <> ω -> bt_merge ⟨r,l⟩ ⟨s,m⟩ = ⟨r,bt_merge l ⟨s,m⟩⟩.
Proof.
  intros E.
  apply bt_merge_graph_fun with (1 := bt_merge_spec _ _).
  constructor; auto.
  apply bt_merge_spec.
Qed.

Check bt_merge_spec_1.
Check bt_merge_spec_2.
Check bt_merge_spec_3.
Check bt_merge_spec_4.

Reserved Notation "x ⋗ y" (at level 70, no associativity).

Inductive bt_msort_graph : bt -> bt -> Prop :=
  | in_btmsg_0 : ω ⋗ ω
  | in_btmsg_1 : forall t, ⟨t,ω⟩ ⋗ ⟨t,ω⟩
  | in_btmsg_2 : forall l l1 l2 m1 m2 p, 2 <= bt_length l 
                              -> bt_split l = ⟨l1,l2⟩
                              -> l1 ⋗ m1
                              -> l2 ⋗ m2
                              -> m1 ⊕ m2 ⊳ p
                              -> l ⋗ p
where "x ⋗ y" := (bt_msort_graph x y).

Fact bt_msort_fun l p1 p2 : l ⋗ p1 -> l ⋗ p2 -> p1 = p2.
Proof.
  intros H1; revert H1 p2.
  induction 1; inversion 1; subst; auto; simpl in *; try lia.
  rewrite H0 in H4; inversion H4; subst l3 l4.
  apply IHbt_msort_graph1 in H5.
  apply IHbt_msort_graph2 in H6.
  subst m0 m3.
  revert H1 H7; apply bt_merge_graph_fun.
Qed.

Fact bt_msort_full l : { p | l ⋗ p }.
Proof.
  induction on l as IHl with measure (bt_length l).
  case_eq l.
  1: { intros E; exists l; subst; constructor. }
  intros t1 [ | t2 m ] E.
  1: { exists l; subst; constructor. }
  generalize (bt_split_length l).
  case_eq (bt_split l).
  1: tauto.
  intros l1 l2 H1 (H2 & H3).
  destruct (IHl l1) as (m1 & H4).
  1: { subst l; simpl in *; lia. }
  destruct (IHl l2) as (m2 & H5).
  1: { subst l; simpl in *; lia. }
  destruct (bt_merge_full m1 m2) as (p & H6).
  exists p.
  rewrite <- E.
  constructor 3 with l1 l2 m1 m2; auto.
  subst; simpl; lia.
Qed.

Definition bt_msort l := proj1_sig (bt_msort_full l).

Fact bt_msort_spec l : l ⋗ bt_msort l.
Proof. apply (proj2_sig _). Qed.

Fact bt_msort_spec_1 : bt_msort ω = ω.
Proof.
  apply bt_msort_fun with (1 := bt_msort_spec _).
  constructor.
Qed.

Fact bt_msort_spec_2 t : bt_msort ⟨t,ω⟩ = ⟨t,ω⟩.
Proof.
  apply bt_msort_fun with (1 := bt_msort_spec _).
  constructor.
Qed.

Fact bt_msort_spec_3 l : 
         2 <= bt_length l 
      -> match bt_split l with
           | ω       => False
           | ⟨l1,l2⟩ => bt_msort l = bt_merge (bt_msort l1) (bt_msort l2)
         end.
Proof.
  intros H.
  generalize (bt_split_length l).
  case_eq (bt_split l); auto.
  intros l1 l2 E _.
  apply bt_msort_fun with (1 := bt_msort_spec _).
  constructor 3 with l1 l2 (bt_msort l1) (bt_msort l2); auto;
    try apply bt_msort_spec.
  apply bt_merge_spec.
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



