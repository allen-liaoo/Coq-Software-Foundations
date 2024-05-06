From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m:nat, n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity. 
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
    intros m n p.
    assert (A: n+p = p + n).
    { rewrite add_comm. reflexivity. }
    (* incomplete *)
Admitted.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof. 
    intros n.
    induction n as [|n' IHn].
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mul_1_r : forall n:nat,
  n * 1 = n.
Proof. 
    intros n.
    induction n as [|n' IHn].
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mul_dis_add : forall n a b : nat,
    n * (a + b) = n * a + n * b.
Proof. 
    intros n a b.
    induction n as [|n' IHn].
    - simpl. reflexivity.
    - {
        induction b as [|b' IHb].
        - rewrite mul_0_r. rewrite add_0_r. rewrite add_0_r. reflexivity.
        - rewrite <- plus_n_Sm. 
    }
Qed.

Theorem mul_comm_helper : forall n k : nat,
    n * (1 + k) = n + n * k.
Proof.
    intros n k.
    induction k as [|k' IHk].
    - simpl. rewrite mul_0_r. rewrite add_0_r. rewrite mul_1_r. reflexivity.
    - 
    (* rewrite mul_dis_add. rewrite mul_1_r. reflexivity. *)
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
    intros n m.
    induction m as [|m' IHm'].
    - simpl. rewrite mul_0_r. reflexivity.
    - simpl. rewrite <- IHm'. rewrite mul_comm_helper. reflexivity.
Qed.