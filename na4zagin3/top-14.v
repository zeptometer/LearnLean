Require Import Coq.Arith.Plus.

Fixpoint mod2 n :=
  match n with
  | 0 => 0
  | S n' => match mod2 n' with 0 => 1 | S _ => 0 end
  end.

Definition task := forall n, mod2 n = mod2 (n * n).


Lemma mod2_is_0_or_1 : forall n, mod2 n = 0 \/ mod2 n = 1.
Proof.
  intros n.
  induction n.
    left.
    reflexivity.
  destruct IHn.
    right.
    simpl.
    rewrite H.
    reflexivity.
  left.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma mod2_n_m_m : forall n m, mod2 (n + m + m) = mod2 n.
Proof.
  intros n m.
  generalize dependent n.
  induction m; intros n.
    repeat rewrite <-plus_n_O.
    reflexivity.
  repeat rewrite <-plus_n_Sm.
  simpl.
  rewrite IHm.
  destruct (mod2_is_0_or_1 n);
    rewrite H;
    reflexivity.
Qed.


Theorem solution: task.
Proof.
  unfold task.

  intros n.
  induction n.
    reflexivity.
  simpl.

  assert (Heq: n + n * S n = n * n + n + n).
    rewrite <- mult_n_Sm.
    rewrite <- Plus.plus_comm.
    reflexivity.

  rewrite Heq.
  rewrite mod2_n_m_m.
  rewrite IHn.
  reflexivity.
  (* FILL IN HERE *)
Qed.
