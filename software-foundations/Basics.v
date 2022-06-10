Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.


Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.


Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Module NatPlayGround.
  Inductive nat : Type :=
    | O
    | S (n : nat).
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.


  Fixpoint mult (n : nat) (m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.


  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

  Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
  Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : nat_scope.
  Notation "x * y" := (mult x y)
                        (at level 40, left associativity)
                        : nat_scope.
End NatPlayGround.


Fixpoint even (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => even n'
  end.


Definition odd (n : nat) : bool :=
  negb (even n).


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.


Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


Theorem plus_O_n : forall n : nat,
    O + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.


Theorem plus_id_exercise : forall n m o : nat,
    n = m ->
    m = o ->
    n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_n_O : forall n : nat,
    n * O = O.
Proof. Admitted.


Theorem mult_n_O_m_O : forall p q : nat,
    (p * O) + (q * O) = O.
Proof.
  intros p q.
  rewrite mult_n_O.
  rewrite mult_n_O.
  reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative : forall b c : bool,
    (b && c) = (c && b).
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c eqn:Ec.
  - { reflexivity. }
  - { intros H.
      rewrite <- H.
      destruct b.
      - reflexivity.
      - reflexivity. }
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
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

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.
