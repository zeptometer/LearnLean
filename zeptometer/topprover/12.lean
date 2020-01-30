example : ∀ n m, n + m = 1 → (n = 0 ∨ m = 0) := begin
    intros n,
    induction n,
    intros,
    simp,
    intros m,
    rw [nat.add_comm, nat.add_succ],
    intro a,
    have b : m + n_n = 0 := begin
        exact nat.succ_inj a
    end,
    right,
    exact (nat.eq_zero_of_add_eq_zero b).left
end