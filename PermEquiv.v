Require Import PeanoNat List.

Open Scope nat_scope.

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


Definition permutation l l' := forall n:nat, num_oc n l = num_oc n l'.

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
      
(** Questão 1 *)
Lemma perm_to_permutation: forall l l', perm l l' -> permutation l l'.
Proof.
Admitted.

(** Questão 2 *)
Lemma permutation_nil: forall l, permutation nil l -> l = nil.
Proof.
Admitted.

Lemma permutation_sym: forall l l', permutation l l' -> permutation l' l.
Proof.
  intros l l' H.
  unfold permutation in *.
  intro n.
  apply eq_sym.
  apply H.
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

Lemma permutation_comm_app: forall l1 l2, permutation (l1 ++ l2) (l2 ++ l1).
Proof.
  intros l1 l2.
  unfold permutation.
  apply num_oc_app.
Qed.

(** Atividade de frequência - aula 08 *)
Lemma permutation_app_cons: forall l1 l2 a, permutation (l1 ++ a :: l2) (a :: l1 ++ l2).
Proof.
  induction l1.
Admitted.
  
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
Admitted.

(** Questão 4 *)
Lemma permutation_to_perm: forall l l', permutation l l' -> perm l l'.
Proof.
 induction l.
 - admit.
 - intros l' Hequiv.
   generalize dependent a.
   generalize dependent l.
   case l'.
   + Admitted.

Theorem perm_equiv: forall l l', perm l l' <-> permutation l l'.
Proof.
  intros l l'.
  split.
  - apply perm_to_permutation.
  - apply permutation_to_perm.
Qed.

