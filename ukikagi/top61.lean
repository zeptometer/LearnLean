example: ∀ (x y: option nat) (n: nat),
    x = some n -> x = y \/ x = none -> x = y
:=
begin
  intros x y n h1 h2,
  cases h2 with h21 h22,
    exact h21,
  rw [h22] at h1,
  injection h1
end
