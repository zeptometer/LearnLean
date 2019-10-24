example : ∀l: list nat, l ++ [0] ≠ [] := begin
    intro l,
    cases l;
    contradiction
end