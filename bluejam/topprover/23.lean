inductive bin : nat → Prop
| bin_epsilon : bin 0
| bin_0 : ∀ (n: nat), bin n → bin (2 * n)
| bin_1 : ∀ (n: nat), bin n → bin (2 * n + 1)

def is_expressible_in_binary_notation := bin

lemma two_gt_one_ : 2 > 1 :=
begin
    exact dec_trivial
end

lemma two_gt_zero : 2 > 0 :=
begin
    exact dec_trivial
end

example : ∀ (n : nat), is_expressible_in_binary_notation n :=
begin
    intros,
    unfold is_expressible_in_binary_notation,
    apply well_founded.induction nat.lt_wf n _; clear n,
    intros x ih,
    let p := x % 2,
    let q := x / 2,
    have: p = 0 ∨ p = 1,
        apply nat.mod_two_eq_zero_or_one,
    cases x,
        apply bin.bin_epsilon,
    have succ_x_gt_zero: nat.succ x > 0, from nat.zero_lt_succ x,
    have div_2_lt : nat.succ x / 2 < nat.succ x,
        from nat.div_lt_self succ_x_gt_zero two_gt_one_,
    cases this,
        have hoge : p + 2 * q = nat.succ x, from nat.mod_add_div (nat.succ x) 2,
        rw ←hoge,
        rw this,
        rw zero_add,
        apply bin.bin_0 q,
        apply ih q,
        assumption,
    have hoge : p + 2 * q = nat.succ x, from nat.mod_add_div (nat.succ x) 2,
    rw ←hoge,
    rw this,
    rw add_comm,
    apply bin.bin_1 q,
    apply ih q,
    assumption,
end
