inductive bin : nat -> Prop
| bin_epsilon : bin 0
| bin_0 : ∀ n, bin n -> bin (2 * n)
| bin_1 : ∀ n, bin n -> bin (2 * n + 1)

definition is_expressible_in_binary_notation := bin.

lemma zero_or_one {n} (h: n < 2): n = 0 ∨ n = 1
:=
begin
  cases h,
  right, trivial,
  left,
  apply nat.eq_zero_of_le_zero,
  exact nat.le_of_succ_le_succ h_a,
end

lemma two_gt_zero: 2 > 0 := nat.zero_lt_succ 1

lemma half_lt {x} (h: 0 < x): x / 2 < x
:=
begin
  apply (nat.div_lt_iff_lt_mul x x two_gt_zero).2,
  have h: x * 1 < x * 2, from nat.mul_lt_mul_of_pos_left dec_trivial h,
  rw mul_one at h,
  exact h
end

example: ∀ n, is_expressible_in_binary_notation n
:=
begin
  intro n,
  unfold is_expressible_in_binary_notation,
  apply well_founded.induction nat.lt_wf n _; clear n,
  intros x ih,
  let q := x / 2,
  let r := x % 2,
  have hx: x = 2 * q + r, {
    apply symm,
    rw nat.add_comm,
    exact nat.mod_add_div x 2,
  },
  have hq: x = 0 ∨ q < x, {
    cases nat.eq_zero_or_pos x with h0 hp,
      left,
      exact h0,
    right,
    exact half_lt hp
  },
  cases hq with hx0 hqltx, {
    rw hx0,
    exact bin.bin_epsilon,
  },
  have r_lt_two: r < 2, {
    apply nat.mod_lt,
    exact nat.zero_lt_succ 1,
  },
  rw hx,
  cases zero_or_one r_lt_two with hr0 hr1,
  {
    rw hr0,
    simp,
    apply bin.bin_0 q _,
    exact ih q hqltx,
  },
  {
    rw hr1,
    apply bin.bin_1 q _,
    exact ih q hqltx,
  }
end
