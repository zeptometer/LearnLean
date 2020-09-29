def piles : Type := (ℕ × ℕ × ℕ)

inductive take2 : piles → piles → Prop
| take12 : ∀ p q r : ℕ, take2 (nat.succ p, nat.succ q, r) (p, q, r)
| take13 : ∀ p q r : ℕ, take2 (nat.succ p, q, nat.succ r) (p, q, r)
| take23 : ∀ p q r : ℕ, take2 (p, nat.succ q, nat.succ r) (p, q, r)

inductive takeAll : piles → Prop
| takeAllEmpty : takeAll (0, 0, 0)
| takeAllStep : ∀ a b : piles, take2 a b → takeAll b → takeAll a

open nat

def isEven : ℕ → bool
| 0 := true
| 1 := false
| (succ (succ n)) := isEven n

def isTriangular (sum mx : ℕ) : bool :=
    sum ≥ mx * 2

def f (sum mx : ℕ) : bool :=
    isEven sum && isTriangular sum mx

theorem dicidability_of_take_all :
    ∃ f : ℕ → ℕ → bool,
        ∀ p q r, (f (p + q + r) (max p (max q r)) = true) ↔ takeAll (p, q, r)
        := begin
            existsi f,
            sorry
        end
