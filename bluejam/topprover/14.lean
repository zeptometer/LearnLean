open nat

def mod2 : nat → nat
| 0 := 0
| (succ n) := 
  match mod2 n with
  | 0 := 1
  | (succ n) := 0
  end

lemma add2 : ∀ (n : nat), mod2 (n + 2) = mod2 n :=
begin
  intros,
  unfold mod2,
  induction n,
    simp [mod2],
  simp [mod2, n_ih]
end

lemma lem : ∀ (k n: nat), mod2 (n + k + k) = mod2 n :=
begin
    intro k, induction k,
        simp [mod2],
    intros,
    show mod2 (n + succ k_n + succ k_n) = mod2 n, from calc
    mod2 (n + succ k_n + succ k_n)
        = mod2 (n + (k_n + 1) + (k_n + 1)) : by refl
    ... = mod2 ((n + k_n + k_n) + 2) : by simp [add_comm, add_assoc]
    ... = mod2 (n + k_n + k_n) : by rw add2
    ... = mod2 n : by rw k_ih
end

example : ∀ (n : nat), mod2 n = mod2 (n * n) :=
begin
    intros,
    induction n,
        simp,
    simp [mul_succ, succ_mul],
    rw (add_comm (succ n_n)),
    rw ←(add_assoc n_n),
    rw add_succ,
    unfold mod2,
    have: mod2 (n_n + n_n * n_n + n_n) = mod2 n_n, from calc
    mod2 (n_n + n_n * n_n + n_n) = mod2 (n_n * n_n + n_n + n_n) : by simp [add_assoc, add_comm]
    ... = mod2 (n_n * n_n) : by rw (lem n_n (n_n * n_n))
    ... = mod2 n_n : by simp [n_ih],
    simp only [this],
end
