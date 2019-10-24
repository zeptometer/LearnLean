example (p q r : Prop) (hp : p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
  split,
    left,
    assumption,
  split,
    right,
    left,
    assumption,
  right,
  right,
  assumption
end

example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by repeat { split <|> { try {left}, assumption } <|> right }
