Require Import Coq.Arith.Peano_dec.

Definition injective1 (f : nat -> nat) : Prop :=
  forall m n, f m = f n -> m = n.

Definition injective2 (f : nat -> nat) : Prop :=
  forall m n, m <> n -> f m <> f n.

Definition task := forall f, injective1 f <-> injective2 f.


Theorem solution: task.
Proof.
  unfold task.
  (* FILL IN HERE *)

  intro f.
  unfold injective1.
  unfold injective2.
  split; intros HI m n H.
    intros Hinv.
    apply H.
    apply HI.
    assumption.
  destruct (dec_eq_nat m n) as [|Hneq].
    assumption.
  remember (HI m n Hneq) as Hcontra.
  contradiction.
Qed.
