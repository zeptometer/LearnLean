open nat

def mod2 : nat → nat
| 0 := 0
| (succ n) := 
  match mod2 n with
  | 0 := 1
  | (succ n) := 0
  end

lemma h1 : ∀ (n : nat), mod2 (n + 2) = mod2 n :=
begin
  intros,
  unfold mod2,
  induction n,
    simp [mod2],
  simp [mod2, n_ih]
end

theorem task : ∀ (n : nat), mod2 n = mod2 (n * n) :=
begin
  intros,
  
end
