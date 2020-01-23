example : forall (n m : nat), n < m \/ n = m \/ n > m :=
begin
    intros,
    have h : n < m ∨ n ≥ m, from lt_or_ge n m,
    cases h,
        left,
        assumption,
    right,
    have : m = n ∨ m < n, from nat.eq_or_lt_of_le h,
    cases this,
        left,
        symmetry,
        assumption,
    right,
    apply this,
end
