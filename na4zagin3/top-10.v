Require Import List.

Fixpoint prefix_sum sum l :=
  match l with
  | nil => sum :: nil
  | head :: tail => sum :: prefix_sum (sum + head) tail
  end.

Fixpoint plus_list l1 l2 :=
  match (l1, l2) with
  | (nil, _) => nil
  | (_, nil) => nil
  | (h1 :: t1, h2 :: t2) => (h1 + h2) :: plus_list t1 t2
  end.

Definition task :=
  forall l1 l2,
    prefix_sum 0 (plus_list l1 l2) =
    plus_list (prefix_sum 0 l1) (prefix_sum 0 l2).

Theorem solution: task.
Proof.
  unfold task.
  assert (plus_list_nil_r : forall l,
    plus_list l nil = nil). {
    intro l; case l; reflexivity.
  }
  assert (generic : forall l1 l2, forall n m,
    prefix_sum (n + m) (plus_list l1 l2) =
    plus_list (prefix_sum n l1) (prefix_sum m l2)). {
    intro l1. induction l1.
      intro l2. induction l2; intros n m; reflexivity.
    intro l2. case l2.
      intros n m.
      simpl.
      rewrite plus_list_nil_r.
      reflexivity.
    intros x l2' n m.
    simpl.
    rewrite <- IHl1.
    rewrite PeanoNat.Nat.add_shuffle1.
    reflexivity.
  }
  intros l1 l2.
  rewrite <- generic.
  reflexivity.
  (* FILL IN HERE *)
Qed.
