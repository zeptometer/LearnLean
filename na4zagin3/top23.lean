inductive bin : nat -> Prop
| bin_epsilon : bin 0
| bin_0 : forall n, bin n -> bin (2 * n)
| bin_1 : forall n, bin n -> bin (2 * n + 1)
  .
def is_expressible_in_binary_notation := bin.

#check nat.mod_lt


theorem top23 : forall n, is_expressible_in_binary_notation n :=
begin
  intro n,
  unfold is_expressible_in_binary_notation,
  apply well_founded.induction nat.lt_wf n _ ; clear n,
  intros x ih,
  have h_x := nat.mod_add_div x 2,
  cases x,
    apply bin.bin_epsilon,
  cases nat.mod_two_eq_zero_or_one (nat.succ x),
    rewrite h at h_x,
    simp at h_x,
    have h_h: bin (nat.succ x / 2), {
      apply ih,
      apply nat.div_lt_self; exact dec_trivial,
    },
    rw [←h_x],
    apply bin.bin_0,
    assumption,
  rw [h] at h_x,
  have h_h: bin (nat.succ x / 2), {
    apply ih,
    apply nat.div_lt_self; try { exact dec_trivial },
  },
  rw [←h_x],
  rw [add_comm],
  apply bin.bin_1,
  assumption,
end.
