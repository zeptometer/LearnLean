inductive bin : ℕ → Prop
| bin_epsilon : bin 0
| bin_0 : ∀ n, bin n → bin (2 * n)
| bin_1 : ∀ n, bin n → bin (2 * n + 1)

definition is_expressible_in_binrary_notation := bin

example : ∀ n, is_expressible_in_binrary_notation n := begin
    intro,
    induction n,
    apply bin.bin_epsilon,
    induction n_ih,
    exact (bin.bin_1 0 bin.bin_epsilon),
    have pohe : (nat.succ (2 * n_ih_n)) = (2 * n_ih_n + 1), begin
        rw ← nat.add_one
    end,
    rw pohe,
    exact bin.bin_1 n_ih_n n_ih_a,
    have fuga: (nat.succ (2 * n_ih_n + 1)) = 2 * (nat.succ n_ih_n), begin
        calc
        (nat.succ (2 * n_ih_n + 1)) = 2 * n_ih_n + 1 + 1 : by rw nat.add_one
        ... = 2 * n_ih_n + (1 + 1) : by rw nat.add_assoc
        ... = 2 * n_ih_n + 2 : by simp
        ... = 2 * n_ih_n + 2 * 1 : by simp
        ... = 2 * (n_ih_n + 1) : by rw nat.left_distrib
        ... = 2 * (nat.succ n_ih_n) : by rw nat.add_one
    end,
    rw fuga,
    exact bin.bin_0 (nat.succ n_ih_n) n_ih_ih
end
