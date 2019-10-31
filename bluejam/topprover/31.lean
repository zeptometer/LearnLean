def binom: ℕ → ℕ → ℕ
| _ 0 := 1
| 0 _ := 0
| (m + 1) (n + 1) := binom m (n + 1) + binom m n

def binom_sum: ℕ → ℕ → ℕ
| n 0 := binom n 0
| n (k + 1) := binom_sum n k + binom n (k + 1)

lemma is_zero: ∀ k, binom 0 (k + 1) = 0 :=
begin
    intros,
    induction k,
        simp [binom],
    assumption
end

lemma binom_sum_zero: ∀ (n : ℕ), binom_sum 0 n = 1 :=
begin
    intros,
    induction n,
        simp [binom_sum, binom],
    simp [binom_sum, binom],
    rw [n_ih, is_zero]
end

lemma binom_exceeds: ∀ (n : ℕ), ∀ (k : ℕ), binom n (n + 1 + k) = 0 :=
begin
    intro n,
    induction n,
        simp [is_zero],
    intros,
    rw [←nat.add_one],
    calc  binom (n_n + 1) ((n_n + 1 + 1) + k)
        = binom (n_n + 1) ((n_n + 1) + (1 + k)) : by rw [nat.add_assoc]
    ... = binom (n_n + 1) ((n_n + 1) + (k + 1))
            : by rw [nat.add_comm 1 k]
    ... = binom (n_n + 1) ((n_n + 1 + k) + 1)
            : by rw [←nat.add_assoc]
    ... = binom n_n (n_n + 1 + k + 1) + binom n_n (n_n + 1 + k)
            : by unfold binom
    ... = binom n_n (n_n + 1 + k + 1) + 0 : by rw [n_ih]
    ... = binom n_n (n_n + 1 + k + 1) : by rw [nat.add_zero]
    ... = binom n_n (n_n + 1 + (k + 1)) : by rw [nat.add_assoc]
    ... = 0 : by rw [n_ih]
end

lemma binom_sum_continue: ∀ n, binom_sum n (n + 1) = binom_sum n n :=
begin
    intros,
    simp [binom_sum, binom_exceeds n 0],
end

lemma binom_sum_split: ∀ (n: ℕ), ∀ (k: ℕ), binom_sum (n + 1) (k + 1)
    = binom_sum n (k + 1) + binom_sum n k :=
begin
    intro n, induction n,
        intro k, induction k,
            simp [binom, binom_sum],
        rw [binom_sum_zero] at *,
        simp * at *,
        assumption,
    intro k, induction k,
        simp [binom_sum, binom],
    calc  binom_sum (nat.succ n_n + 1) (nat.succ k_n + 1)
        = binom_sum (nat.succ n_n + 1) (nat.succ k_n)
          + binom (nat.succ n_n + 1) (nat.succ k_n + 1)
            : by rw binom_sum
    ... = binom_sum (nat.succ n_n) (k_n + 1) + binom_sum (nat.succ n_n) k_n
          + binom (nat.succ n_n + 1) (nat.succ k_n + 1)
            : by rw k_ih
    ... = (binom_sum (nat.succ n_n) (k_n + 1) + binom_sum (nat.succ n_n) k_n)
          + binom (nat.succ n_n) (nat.succ k_n + 1) + binom (nat.succ n_n) (nat.succ k_n)
            : by simp [binom]
    ... = (binom_sum (nat.succ n_n) (k_n + 1) + binom (nat.succ n_n) (nat.succ k_n + 1))
          + (binom_sum (nat.succ n_n) k_n) + binom (nat.succ n_n) (nat.succ k_n)
            : by simp [nat.add_assoc, nat.add_comm]
    ... = binom_sum (nat.succ n_n) (nat.succ k_n + 1)
           + binom_sum (nat.succ n_n) (nat.succ k_n)
            : by simp [binom_sum]
end

example: ∀ (n: ℕ), binom_sum n n = 2^n :=
begin
    intros,
    induction n,
        simp [binom_sum, binom],
    simp [binom_sum_split],
    simp [binom_sum_continue],
    simp *,
    calc 2 ^ n_n + 2 ^ n_n
        = 1 * 2 ^ n_n + 2 ^ n_n : by rw nat.one_mul
    ... = 2 * 2 ^ n_n : by rw ←nat.succ_mul
    ... = 2 ^ n_n * 2 : by rw ←mul_comm
    ... = 2 ^ nat.succ n_n : by rw nat.pow_succ
end
