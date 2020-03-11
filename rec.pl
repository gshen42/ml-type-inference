:- op(700, xfy, →).
:- op(900, xfx, :).
:- op(910, xfx, ⊢).
:- op(920, xfx, ∈).
:- op(300, yfx, $).

X ∈ [X | _] :- !.
X ∈ [_ | L] :- X ∈ L.

Γ ⊢ var(X) : Ty :-
    (X:Ty) ∈ Γ, !.

Γ ⊢ lam(X, T2) : Ty1 → Ty2 :-
    [X:Ty1 | Γ] ⊢ T2 : Ty2.

Γ ⊢ T1 $ T2 : Ty2 :-
    Γ ⊢ T1 : Ty1 → Ty2,
    Γ ⊢ T2 : Ty1.

/*
Examples:

term: λx. x x
query: [] ⊢ lam(x, var(x) $ var(x)) : Ty.

Omega:
term: (λx. x x) (λx. x x)
query: [] ⊢ lam(x, var(x) $ var(x)) $ lam(x, var(x) $ var(x)) : Ty.

Call-by name Y combinator:
term: λf. (λx. f (x x)) (λx. f (x x))
query: [] ⊢ lam(f, lam(x, var(f) $ (var(x) $ var(x))) $ lam(x, var(f) $ (var(x) $ var(x)))) : Ty.
*/
