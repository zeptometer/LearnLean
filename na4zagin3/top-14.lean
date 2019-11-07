def mod2 : ℕ → ℕ
| 0 := 0
| (nat.succ n) := match mod2 n with
    | 0 := 1
    | (nat.succ _) := 0
    end.

open nat

theorem mod2_0 : mod2 0 = 0 :=
begin
  simp [mod2],
end.

theorem mod2_1 : mod2 1 = 1 :=
begin
  simp [mod2],
end.

theorem mod2_return_0_1 : ∀ n, mod2 n = 0 ∨ mod2 n = 1 :=
begin
  intro n,
  induction n,
    left,
    unfold mod2,
  cases n_ih,
    right,
    unfold mod2,
    rw n_ih,
    unfold mod2._match_1,
  left,
  unfold mod2,
  rw n_ih,
  unfold mod2._match_1,
end.

theorem mod2_mul_2_0 : ∀ n,  mod2 (2 * n) = 0 :=
begin
  intro n,
  induction n with n Hn,
    simp [mod2],
  rw [mul_succ],
  unfold mod2,
  rw Hn,
  unfold mod2._match_1,
end.

theorem mod2_idempotent : ∀ n,  mod2 (mod2 n) = mod2 n :=
begin
  intro n,
  cases (mod2_return_0_1 n); simp [h, mod2],
end.

theorem mod2_add_homo : ∀ n m,  mod2 (n + m) = mod2 (mod2 n + mod2 m) :=
begin
  intros n m,
  revert n,
  induction m with m IH; intros n,
    simp [mod2, mod2_idempotent],
  unfold mod2,
  rewrite IH,
  cases (mod2_return_0_1 n) with Hn Hn;
    cases (mod2_return_0_1 m) with Hm Hm;
    simp [Hn, Hm, mod2],
end.

theorem sq_succ_n {n: nat} : (n+1) * (n+1) = n * n + 2 * n + 1 :=
begin
  simp,
  rw [nat.mul_succ, nat.mul_comm, nat.mul_succ],
  have H2n : 2 * n = n + n,
    rw [nat.mul_comm, nat.mul_succ, nat.mul_one],
  rw [H2n],
  simp [add_comm],
end.

example : ∀ n, mod2 n = mod2 (n * n) :=
begin
  intro n,
  induction n with n,
    simp [mod2],
  simp [mod2],
  rw [sq_succ_n, mod2_add_homo, mod2_1],
  unfold mod2,
  rw [mod2_add_homo, ←n_ih, mod2_mul_2_0, add_zero],
  simp [mod2_idempotent],
end.
