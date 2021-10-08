From LF Require Export Basics.

Theorem add_0_r : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - { simpl.  rewrite -> IHn'. reflexivity. }
Qed.

Theorem minus_n_n : forall n,
    minus n n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - { simpl. rewrite -> IHn'. reflexivity. }
Qed.

Theorem mul_0_r : forall n : nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
    double n = n + n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - { simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. }
Qed.

Theorem even_S : forall n : nat,
    even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - { rewrite -> IHn'.
      rewrite -> negation_fn_applied_twice.
      simpl.
      reflexivity.
      reflexivity. }
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). {
    rewrite add_comm.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  assert (H: n + m = m + n). { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.


Theorem mult_Sm_n : forall n m : nat,
    (1 + n) * m = m + n * m.
Proof.  
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

  
Theorem mul_comm : forall n m : nat,
    m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - rewrite mul_0_r. reflexivity.
  - {
      rewrite <- plus_1_l.
      rewrite <- mult_n_Sm.
      rewrite mult_Sm_n.
      rewrite IHn'.
      rewrite add_comm.
      reflexivity.
    }
Qed.

Theorem leb_refl : forall n : nat,
    (n <=? n) = true.
Proof.  
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n : nat,
    0 =? (S n) = false.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHn'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
    1 * n = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite add_comm. rewrite plus_O_n. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b) (negb c))
    = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - { simpl.
      { destruct c eqn:Ec.
        - reflexivity.
        - reflexivity. } }
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p  = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p' IHn'].
Admitted.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.  
  intros n m p.
  induction n as [| n' IHn'].
  -  reflexivity.
  - {
      rewrite <- plus_1_l.
      rewrite mult_plus_distr_r.
      rewrite mult_plus_distr_r.
      rewrite mult_plus_distr_r.
      simpl.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O.
      rewrite mul_comm.
Admitted.
