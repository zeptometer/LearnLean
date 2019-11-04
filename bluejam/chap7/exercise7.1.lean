namespace hidden

inductive nat : Type
| zero : nat
| succ : nat → nat

namespace nat

def add (m n : nat) : nat :=
nat.rec_on n m (fun n add_m_n, succ add_m_n)

instance : has_zero nat := has_zero.mk zero
instance : has_add nat := has_add.mk add

theorem add_zero (m : nat) : m + nat.zero = m := rfl
theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : nat) : nat.zero + n = n :=
nat.rec_on n rfl (λ n ih, by rw [add_succ, ih])

theorem add_assoc (m n k : nat) : m + n + k = m + (n + k) :=
nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])

theorem succ_add (m n : nat) : succ m + n = succ (m + n) :=
nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])

theorem add_comm (m n : nat) : m + n = n + m :=
nat.rec_on n
  (begin
    simp only [zero_add, add_zero]
  end)
  (λ n ih, by simp only [add_succ, ih, succ_add])

-- Exercise

def mul (m n : nat) : nat :=
nat.rec_on n 0 (λ n mul_m_n, mul_m_n + m)

def pred (n : nat) : nat :=
nat.rec_on n 0 (λ n x, n)

def sub (m n : nat) : nat :=
nat.rec_on n m (λ n sub_m_n, pred sub_m_n)

instance : has_mul nat := has_mul.mk mul
instance : has_sub nat := has_sub.mk sub
instance : has_one nat := has_one.mk (succ zero)

def pow (m n : nat) : nat :=
nat.rec_on n (succ zero) (λ n pow_m_n, pow_m_n * m)

theorem mul_zero (n : nat) : n * zero = zero := rfl
theorem mul_succ (n m : nat) : n * (succ m) = (n * m) + n := rfl

theorem zero_mul (n : nat) : zero * n = zero :=
begin
    induction n,
        refl,
    show zero * succ n_a = zero, from
    calc zero * succ n_a
        = (zero * n_a) + zero : by rw mul_succ
    ... = zero * n_a : by rw add_zero
    ... = zero : n_ih
end

theorem one_mul (n : nat) : (succ zero) * n = n :=
begin
    induction n,
        refl,
    rw mul_succ,
    rw n_ih,
    refl
end

theorem mul_one (n : nat) : n * (succ zero) = n :=
begin
    induction n,
        rw zero_mul,
    rw mul_succ,
    rw [mul_zero, zero_add]
end

theorem mul_dist (m n k : nat) : m * n + m * k = m * (n + k) :=
begin
    induction k,
        simp [add_zero, mul_zero],
    simp [mul_succ],
    rw [←add_assoc],
    rw k_ih,
    rw ←mul_succ,
    rw add_succ
end

theorem mul_assoc (m n k : nat) : (m * n) * k = m * (n * k) :=
begin
    induction k,
        simp [mul_zero],
    simp [mul_succ, k_ih],
    simp [mul_dist]
end

theorem succ_mul (n m : nat) : (succ n) * m = (n * m) + m :=
begin
    induction m,
        simp [mul_zero, add_zero],
    simp [mul_succ, m_ih],
    simp [add_succ],
    simp [add_assoc, add_comm m_a n]
end

theorem mul_comm (m n : nat) : m * n = n * m :=
begin
    induction n,
        simp [mul_zero, zero_mul],
    simp [mul_succ],
    rw [n_ih],
    simp [succ_mul]
end

theorem dist_mul (m n k : nat) : m * k + n * k = (m + n) * k :=
begin
    simp [mul_comm],
    rw ←mul_dist,
    simp [mul_comm]
end

instance : has_pow nat nat := has_pow.mk pow

theorem pow_succ (m n : nat) : m ^ (succ n) = m ^ n * m := rfl
theorem pow_zero (m : nat) : m ^ zero = (succ zero) := rfl

theorem pow_mul (m n k : nat) : m ^ n * m ^ k = m ^ (n + k) :=
begin
    induction k,
        simp [add_zero, pow_zero, mul_one],
    rw [pow_succ, ←mul_assoc],
    rw k_ih,
    rw [←pow_succ],
    rw [add_succ]
end

theorem pow_pow (m n k : nat) : (m ^ n) ^ k = m ^ (n * k) :=
begin
    induction k,
        simp [mul_zero, pow_zero],
    simp [pow_succ],
    rw k_ih,
    simp [pow_mul, mul_succ]
end

end nat

end hidden
