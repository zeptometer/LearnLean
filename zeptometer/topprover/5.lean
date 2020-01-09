open nat

example : ∀ n m, n * succ m = n + n * m := begin
    intros,
    rw [mul_succ, add_comm]
end
