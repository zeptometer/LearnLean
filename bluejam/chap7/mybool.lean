namespace hidden
inductive bool : Type
| ff : bool
| tt : bool

open hidden.bool

def band (b1 b2 : bool) : bool :=
bool.cases_on b1 ff b2

def bnot (b1 : bool) : bool :=
bool.cases_on b1 tt ff

def bor (b1 b2 : bool) : bool :=
bool.cases_on b1 b2 tt

theorem band_comm (b1 b2 : bool) : band b1 b2 = band b2 b1 :=
begin
    cases b1; cases b2; apply rfl
end

theorem bor_comm (b1 b2 : bool) : bor b1 b2 = bor b2 b1 :=
begin
    cases b1; cases b2; apply rfl
end

theorem band_assoc (a b c : bool) : band (band a b) c = band a (band b c) :=
begin
    cases a; cases b; cases c; apply rfl
end

theorem de_morgan (a b : bool) : bnot (band a b) = bor (bnot a) (bnot b) :=
begin
    cases a; cases b; apply rfl
end

end hidden
