theorem plus_comm : ∀ n m : nat, n + m = m + n := begin
    intros,
    apply nat.add_comm
end