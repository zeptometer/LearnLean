def injective1 (f : nat -> nat) : Prop :=
  forall m n, f m = f n -> m = n.

def injective2 (f : nat -> nat) : Prop :=
  forall m n, m ≠ n -> f m ≠ f n.

example : ∀ f, injective1 f ↔ injective2 f :=
begin
  intro f,
  unfold injective1,
  unfold injective2,
  split; intros HI m n H,
    intros Hinv,
    apply H,
    apply HI,
    assumption,
  cases nat.decidable_eq m n,
    have Hcontra := HI m n h,
    contradiction,
  assumption,
end.
