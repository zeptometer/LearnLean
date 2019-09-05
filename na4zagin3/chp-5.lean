section sec_3_redo
open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  split; {
    intro h,
    cases h with p q,
    split; assumption
  }
end
example : p ∨ q ↔ q ∨ p :=
begin
  split; {
    intro h,
    cases h with p q; { left; assumption } <|> { right; assumption }
  }
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  split; {
    intro h,
    cases h with h1 h2,
    cases h1 with h11 h12 <|> cases h2 with h22 h23,
    repeat { split }; assumption,
  }
end
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  split; {
    intro h,
    cases h; try { cases h },
    all_goals {
      { repeat { { left; assumption } <|> right }; assumption } <|>
      { repeat { { right; assumption } <|> left }; assumption } }
  }
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  split,
    intros h,
    cases h with hp hqr,
    cases hqr with hq hr;
    { left; split; assumption } <|> { right; split; assumption },
  intros h,
  cases h; cases h with hq hqr; split;
  { assumption <|> { left; assumption}  <|> { right; assumption} }
end
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
end sec_3_redo

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by split; split <|> left; assumption <|> right; {left; assumption} <|> {right; assumption}

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
  split,
  all_goals { try {split} },
  all_goals { repeat { {left; assumption} <|> right } },
  all_goals { assumption },
end

