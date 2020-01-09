example: ∀ (f: bool -> bool) b, f (f (f b)) = f b
:=
begin
    intros f b,
    cases b; cases ht: f tt; cases hf: f ff,
    repeat {
        try {rw ht},
        try {rw hf},
    },
end
