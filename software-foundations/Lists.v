From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Check (pair 3 5) : natprod.
Check (3, 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | (n1, n2) => n1
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | (n1, n2) => n2
  end.


Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x, y) => (y, x)
  end.


Theorem surjective_pairing' : forall (n m : nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof. reflexivity. Qed.

Theorem surjective_pair : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.


Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros p.
  rewrite <- snd_fst_is_swap.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).


Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                    (at level 60, right associativity).
Notation "[  ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: 2 :: 3 :: nil.
Definition mylist2 := [1; 2; 3].

Compute mylist1.
Compute mylist2.


Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.


Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match h with
                | O => nonzeros t
                | S n' => h :: nonzeros t
              end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.


Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match (odd h) with
                | false => oddmembers t
                | true => h :: oddmembers t
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.


Definition countoddmembers (l : natlist) : nat :=
    length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | (h1 :: t1), (h2 :: t2) => app [h1; h2] (alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.


Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => O
    | h :: t => match (eqb h v) with
                | true => S (count v t)
                | false => count v t
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.


Definition sum : bag -> bag -> bag := alternate.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  app [v] s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.


Definition member (v : nat) (s : bag) : bool :=
  match (count v s) with
    | O => false
    | S _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => match (eqb h v) with
                | true => t
                | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => match (eqb h v) with
                | true => remove_all v t
                | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
    | nil => true
    | h :: t => match (member h s2) with
                | true => subset t (remove_one h s2)
                | false => false
              end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


Theorem add_inc_count : forall (n : nat) (s : bag),
    length (add n s) = S (length s).
Proof.
  intros n s.
  simpl.
  reflexivity.
Qed.


Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.


Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => rev t ++ [h]
  end.


Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.


Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - { simpl.
      rewrite -> app_length.
      rewrite -> IHl'.
      simpl.
      rewrite -> add_comm.
      reflexivity.
    }
Qed.


Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.


Theorem rev_app_distr : forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1 IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.
Qed.


Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.


Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n1 l1' IHl1'].
  - reflexivity.
  - { simpl.
      destruct n1.
      - rewrite -> IHl1'. reflexivity.
      - simpl. rewrite -> IHl1'. reflexivity.
    }
Qed.


Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
          | nil => true
          | h2 :: t2 => false
          end
  | h1 :: t1 => match l2 with
            | nil => false
            | h2 :: t2 => match (eqb h1 h2) with
                        | true => eqblist t1 t2
                        | false => false
                        end
            end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l : natlist,
    true = eqblist l l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - { simpl.
      assert (eqb_refl: eqb n n = true).
      { induction n as [| n' IHn'].
        - reflexivity.
        - simpl. rewrite -> IHn'. reflexivity.
      }
      rewrite -> eqb_refl.
      rewrite -> IHl'.
      reflexivity.
    }
Qed.


Theorem count_members_nonzero : forall (s : bag),
    leb 1 (count 1 (1 :: s)) = true.
Proof. reflexivity. Qed.


Theorem leb_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count : forall (s : bag),
    leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  Admitted.


Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  rewrite <- rev_involutive.
  replace l1 with (rev (rev l1)).
  rewrite -> H.
  reflexivity.

  (* l1 = rev (rev l1) *)
  rewrite -> rev_involutive. reflexivity.
Qed.


Inductive natoption : Type :=
  | Some (n : nat)
  | None.
