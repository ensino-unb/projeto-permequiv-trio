(* Projeto LC1*)
(* Alunos: Vincius Lima Passos (200028545) / Marcelo Junqueira Ferreira (200023624) / Davi de Moura Amaral (200016750) *)

Require Import PeanoNat List.
Open Scope nat_scope.

(* Definições*)

Fixpoint insere (n:nat) (l: list nat) :=
  match l with
  | nil => n :: nil (* lista unitária *)
  | h :: tl => if n <=? h then (n :: l) (* inserção de n na primeira posição *)
             else (h :: (insere n tl)) (* inserção de n na cauda da lista *)
  end.

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl 
  end.

Lemma num_oc_S: forall n l1 l2, num_oc n (l1 ++ n :: l2) = S (num_oc n (l1 ++ l2)).
Proof.
  induction l1.
  - intro l2.
    simpl.
    rewrite Nat.eqb_refl; reflexivity.
  - intro l2.
    simpl.
    destruct (n =? a); rewrite IHl1; reflexivity.
Qed.

Lemma num_oc_neq: forall n a l1 l2, n =? a = false -> num_oc n (l1 ++ a :: l2) = num_oc n (l1 ++ l2).
Proof.
  induction l1.
  - intros l2 H.
    simpl.
    rewrite H.
    reflexivity.
  - intros l2 Hfalse.
    simpl.
    destruct (n =? a0) eqn:H.
    + apply (IHl1 l2) in Hfalse.
      rewrite Hfalse; reflexivity.
    + apply (IHl1 l2) in Hfalse.
      assumption.
Qed.

Lemma num_oc_app: forall l1 l2 n, num_oc n (l1 ++ l2) = num_oc n (l2 ++ l1).
Proof.
  induction l1.
  - intros l2 n.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - intros l2 n.
    simpl.
    destruct (n =? a) eqn:H.
    + apply Nat.eqb_eq in H; subst.
      rewrite num_oc_S.
      rewrite IHl1.
      reflexivity.
    + rewrite num_oc_neq.
      * rewrite IHl1.
        reflexivity.
      * assumption.
Qed.


(*permutation*)
Definition permutation l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma permutation_refl: forall l, permutation l l.
Proof.
  intro l.
  unfold permutation.
  intro x.
  reflexivity.
Qed.

(* Questão 2 ----- *)

Lemma permutation_nil: forall l, permutation nil l -> l = nil.
Proof.
  intro l.
  case l.
  - intro H.
    reflexivity.
  - intros n l' H.
    unfold permutation in H.
    specialize (H n).
    simpl in H.
    rewrite Nat.eqb_refl in H.
    inversion H.
Qed.

Lemma permutation_sym: forall l l', permutation l l' -> permutation l' l.
Proof.
  intros l l' H.
  unfold permutation in *.
  intro n.
  apply eq_sym.
  apply H.
Qed.

Lemma permutation_trans: forall l1 l2 l3, permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Proof.
  intros.
  induction l1.
  -apply permutation_nil in H.
   rewrite H in H0.
   assumption. 
  -unfold permutation in *.
   simpl in *.
   intros n.
   assert (H := H n).
   destruct (n =? a) in *.
   + rewrite H.
     apply H0.
   + rewrite H.
     apply H0.
Qed.

Lemma permutation_hd: forall l l' x, permutation l l' -> permutation (x :: l) (x :: l').
Proof.
  intros l l' x H.
  unfold permutation in *.
  intro x'.
  destruct (x'=?x) eqn:H'.
  -simpl.
    rewrite H'.
    rewrite H.
    reflexivity.
  -simpl.
    rewrite H'.
    rewrite H.
    reflexivity.
Qed.

Lemma permutation_hd_back: forall l l' x, permutation (x::l) (x::l') -> permutation l l'.
Proof.
  intros l l' x H.
  unfold permutation in *. 
  intro x'.
  specialize (H x').
  simpl in H.
  destruct (x' =? x)eqn: J.
  +  apply eq_add_S in H.
    assumption.
  + assumption.
Qed.

Lemma permutation_2head: forall l x y, permutation ( x::y::l)(y::x::l).
Proof.
  intros l x y.
  unfold permutation.
  intro x0.
  simpl.
  destruct (x0 =? x) eqn:H.
  +destruct(x0 =? y) eqn:J.
    -reflexivity.
    -reflexivity.
  +destruct(x0 =? y) eqn:J.
    -reflexivity.
    -reflexivity.
Qed.

Lemma permutation_insere: forall l l' x, permutation l l' -> permutation (x :: l) (insere x l').
Proof.
  intros l l' x H.
  simpl.
  generalize dependent x.
  generalize dependent l.
  induction l'.
  - intros l H x.
    apply permutation_sym in H.
    apply permutation_nil in H.
    rewrite H.
    simpl.
    apply permutation_refl.
  - intros l H x.
    apply permutation_trans with (x :: a :: l').
    +apply permutation_hd.
      assumption.
    +simpl.
      destruct (x <=? a) eqn:J.
      *apply permutation_refl.
      *apply permutation_trans with (a :: x :: l').
        ** unfold permutation in *.
           apply permutation_2head.
        **apply permutation_hd.
           apply IHl'.
           apply permutation_refl.
Qed.


(*perm*)
Inductive perm: list nat -> list nat -> Prop :=
| perm_refl: forall l, perm l l
| perm_hd: forall x l l', perm l l' -> perm (x::l) (x::l')
| perm_swap: forall x y l l', perm l l' -> perm (x::y::l) (y::x::l')
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Lemma perm_app_cons: forall l1 l2 a, perm (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  induction l1.
  - intros l2 a.
    simpl.
    apply perm_refl.
  - intros l2 a'.
    simpl.
    apply perm_trans with (a :: a' :: l1 ++ l2).
    + apply perm_swap.
      apply perm_refl.
    + apply perm_hd.
      apply IHl1.
Qed.

Lemma perm_insere: forall l x, perm (x :: l) (insere x l).
 Proof.
   induction l.
   - intro x.
     simpl.
     apply perm_refl.
   - intro x.
     simpl.
     destruct (x <=? a).
     + apply perm_refl.
     + apply perm_trans with (a :: x :: l).
       * apply perm_swap.
         apply perm_refl.
       * apply perm_hd.
         apply IHl.
Qed.      

(** Questão 1 *)

Lemma perm_to_permutation: forall l l', perm l l' -> permutation l l'.
Proof.
  induction 1.
   -apply permutation_refl.
   -apply permutation_hd. apply IHperm.
   -apply permutation_trans with (y::x::l).
     +apply permutation_2head.
     +apply permutation_hd. apply permutation_hd. apply IHperm.
   -apply permutation_trans with l2.
     +assumption.
     +assumption.
Qed.

Lemma permutation_cons: forall n l l', permutation (n :: l) (n :: l') <-> permutation l l'.
Proof.
  intros n l l'; split.
  - intro H.
    unfold permutation in *.
    intro n'.
    assert (H' := H n').
    clear H.
    simpl in *.
    destruct (n' =? n).
    + inversion H'.
      reflexivity.
    + inversion H'.
      reflexivity.
  - intro H.
    unfold permutation in *.
    intro n'.
    simpl.
    destruct (n' =? n).
    + assert (H := H n').
      rewrite H.
      reflexivity.
    + apply H.
Qed.

Lemma permutation_comm_app: forall l1 l2, permutation (l1 ++ l2) (l2 ++ l1).
Proof.
  intros l1 l2.
  unfold permutation.
  apply num_oc_app.
Qed.

Lemma permutation_cons_num_oc: forall n l l', permutation (n :: l) l' -> exists x, num_oc  n l' = S x.
Proof.
  intros.
  unfold permutation in H.
  assert (Hn := H n).
  rewrite <- Hn.
  simpl.
  rewrite Nat.eqb_refl.
  exists (num_oc n l).
  reflexivity.
Qed.

(** Questão 3 *)

Lemma num_occ_cons: forall l x n, num_oc x l = S n -> exists l1 l2, l = l1 ++ x :: l2 /\ num_oc x (l1 ++ l2) = n.
Proof.
  induction l.
  -intros.
    simpl in H.
    inversion H.
  -intros.
    simpl in H.
    destruct (x =? a) eqn: H1.
    +specialize (IHl x n).
      apply Nat.eqb_eq in H1.
      rewrite H1.
      exists nil.
      exists l.
      simpl.
      rewrite H1 in H.
      apply eq_add_S in H.
      split.
      *reflexivity.
      *assumption.
    +apply IHl in H.
      destruct H.
      destruct H.
      destruct H.
      rewrite H.
      exists (a :: x0).
      exists x1.
      split.
      *reflexivity.
      *simpl.
        rewrite H1.
        assumption.
      Qed.

(** Questão 4 *)

Lemma permutation_app_cons: forall l1 l2 a, permutation (a :: l1 ++ l2) (l1 ++ a :: l2). 
Proof.
  intros.
  apply permutation_trans with (a :: l2 ++ l1). apply permutation_hd. apply permutation_comm_app.
  unfold permutation. 
  intros. 
  apply num_oc_app with (l1:=(a::l2)).
Qed.
  
Lemma permutation_to_perm: forall l l', permutation l l' -> perm l l'.
Proof.
  intro l1; elim l1.
  intros.
  apply permutation_nil in H. rewrite H.
  apply perm_refl.
  intros.
  assert (H0' := H0); apply permutation_cons_num_oc in H0'. 
  destruct H0'.
  apply num_occ_cons in H1.
  destruct H1. destruct H1. destruct H1. rewrite H1. 
  apply perm_trans with (a :: x0 ++ x1).
  - apply perm_hd. apply H. apply permutation_hd_back with (x:=a).
    apply permutation_trans with l'.
    -- assumption.
    -- rewrite H1. apply permutation_sym. apply permutation_app_cons.
  - apply perm_app_cons.
Qed.

Theorem perm_equiv: forall l l', perm l l' <-> permutation l l'.
Proof.
  intros l l'.
  split.
  - apply perm_to_permutation.
  - apply permutation_to_perm.
Qed.