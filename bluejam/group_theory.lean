constants (α : Type) (op : α → α → α)

notation a `*` b := op a b

def identity_element (e : α) := ∀ x : α, e * x = x ∧ x * e = x
-- We don't need to define this axiom, because we'll define an identity element later
axiom exists_idetity_element : ∃ e : α, identity_element e
-- Define an element e is identity element
constant e : α
constant identity_e : identity_element e

def inverse (x : α) (y : α) := x * y = e ∧ y * x = e
axiom exists_inverse : ∀ x : α, ∃ y: α, inverse x y
axiom associative_law : ∀  x : α, ∀ y : α, ∀ z : α, (x * y) * z = x * (y * z)

theorem unique_identity_element : ∀ e₁ : α, identity_element e₁ → e₁ = e :=
    assume e₁ : α,
    assume h : identity_element e₁,
    calc e₁ = e₁ * e    : by rw (identity_e e₁).right
        ... = e         : by rw (h e).left

theorem unique_inverse : ∀ x : α, ∀ y : α, ∀ z : α, inverse x y ∧ inverse x z → y = z :=
    assume x : α,
    assume y : α,
    assume z : α,
    assume h : inverse x y ∧ inverse x z,
    calc y  = y * e         : by rw (identity_e y).right
        ... = y * (x * z)   : by rw h.right.left
        ... = (y * x) * z   : by rw associative_law
        ... = e * z         : by rw h.left.right
        ... = z             : by rw (identity_e z).left
