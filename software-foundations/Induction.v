From LF Require Export Basics.

Theorem add_0_r : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem minus_n_n : forall n : nat,
    n - n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem mul_0_r : forall n : nat,
    0 * n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - reflexivity.
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
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm. reflexivity.
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
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem plus_rearrange: forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> add_comm.
    reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


(* Informal Proof of add_comm *)
(* We want to prove n + m = m + n
   We proceed by induction on n
   For the base case n = 0, we want to prove
   that 0 + m = m + 0. We have already prove RHS in
   add_0_r. Rewriting in terms of that we get 0 + m = m.
   This follows from the definition of +.

   Let IHn' be the inductive hypothesis n' + m = m + n'
   We want to prove S n' + m = m + S n'
   We simply the equation to S (n' + m) = m + Sn'
   We rewrite in terms of IHn' to get S (m + n') = m + S n'
   We rewrite in terms of add_plus_Sm to get m + S n' = m + S n'
   Reflexivity
   QED.
*)

Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem mul_0_l : forall n : nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
    m * n = n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite mul_0_l. reflexivity.
  - { simpl.
      rewrite <- mult_n_Sm.
      rewrite IHn'.
      rewrite add_comm.
      reflexivity.
    }
Qed.

Check leb.


Theorem leb_refl : forall n : nat,
    (leb n n) = true.
(* c *)
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n : nat,
    (eqb 0 (S n)) = false.
(* a *)
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
(* b *)
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.


Theorem plus_leb_compat_l : forall n m p : nat,
    (leb n m) = true ->
    (leb (p + n) (p + m)) = true.
(* c *)
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem S_neqb_zero : forall n : nat,
    (eqb (S n) 0) = false.
(* a *)
Proof. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
           (negb c))
      = true.
(* b *)
Proof.
  intros b c.
  destruct b eqn:Eb.
  - { simpl.
      destruct c.
      - reflexivity.
      - reflexivity.
    }
  - { reflexivity. }
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
(* c *)
Proof.
  intros n m p.
  induction p as [| p' IHp'].
  - rewrite mul_0_l. rewrite mul_0_l. rewrite mul_0_l. reflexivity.
  - { rewrite <- mult_n_Sm.
      rewrite <- mult_n_Sm.
      rewrite <- mult_n_Sm.
      rewrite -> IHp'.

      rewrite <- add_assoc.

      assert (H1 : m * p' + (n + m) = (n + m) + m * p').
      { rewrite add_comm. reflexivity. }
      rewrite H1.

      assert (H2 : m * p' + m = m + m * p').
      { rewrite add_comm. reflexivity. }
      rewrite H2.

      rewrite add_assoc.
      rewrite add_assoc.
      rewrite add_assoc.
      reflexivity. }
Qed.


Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite mul_0_r. reflexivity.
  - { simpl.
      rewrite IHn'.
      rewrite mult_plus_distr_r.
      reflexivity.
    }
Qed.


Theorem eqb_refl : forall n : nat,
    (eqb n n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem add_shuffle3' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  replace (n+m) with (m+n).
  reflexivity.

  (* n + m = m + n *)
  { rewrite add_comm. reflexivity. }
Qed.


Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B0 m' => 2 * bin_to_nat m'
  | B1 m' => 1 + 2 * bin_to_nat m'
  end.

(*
Theorem bin_to_nat_pres_incr : forall n : bin,
      bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n.
  destruct n eqn:En.
  - reflexivity.
  - reflexivity.
  - { destruct b eqn:Eb.
      - reflexivity.
      - simpl. rewrite <- plus_n_Sm. reflexivity.
      - { simpl.
          rewrite -> plus_n_Sm.
          rewrite -> plus_n_Sm.
          rewrite -> plus_n_Sm.
          rewrite -> plus_n_Sm.
          rewrite -> add_0_r.
          rewrite -> add_0_r.
          rewrite -> add_0_r.
      }
  *)
