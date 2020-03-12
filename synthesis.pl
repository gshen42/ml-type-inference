:- set_prolog_flag(occurs_check, true).

:- op(700, xfy, →).
:- op(900, xfx, :).
:- op(910, xfx, ⊢).
:- op(920, xfx, ∈).
:- op(300, yfx, $).

X ∈ [X | _] :- !.
X ∈ [_ | L] :- X ∈ L.

Γ ⊢ var(X) : Ty :-
    (X:Ty) ∈ Γ.

% the explicit annotation makes the synthesized term easy to read
Γ ⊢ lamAnn(X, Ty1, T2) : Ty1 → Ty2 :-
    [X:Ty1 | Γ] ⊢ T2 : Ty2.

Γ ⊢ {T1, T2} : Ty1 * Ty2 :-
    Γ ⊢ T1 : Ty1,
    Γ ⊢ T2 : Ty2.

Γ ⊢ inl(T) : Ty1 + Ty2 :-
    Γ ⊢ T : Ty1.

Γ ⊢ inr(T) : Ty1 + Ty2 :-
    Γ ⊢ T : Ty2.

Γ ⊢ T1 $ T2 : Ty2 :-
    Γ ⊢ T1 : Ty1 → Ty2,
    Γ ⊢ T2 : Ty1.

Γ ⊢ fst(T) : Ty1 :-
    Γ ⊢ T : Ty1 * Ty2.

Γ ⊢ snd(T) : Ty2 :-
    Γ ⊢ T : Ty1 * Ty2.

Γ ⊢ case(T, X1, T1, X2, T2) : Ty :-
    Γ ⊢ T : Ty1 + Ty2,
    [(X1:Ty1)| Γ] ⊢ T1 : Ty,
    [(X2:Ty2)| Γ] ⊢ T2 : Ty.

/*
Examples:

Modus ponens:
[] ⊢ T : (a → b) → a → b.

[] ⊢ T : (a * b) → a.

[] ⊢ T : (a * b) → b.

Depth-first search sucks:
[] ⊢ T : (a + b) → (a → c) → (b → c) → c.

[] ⊢ T : (a * b) → (b * a).

[] ⊢ T : (a → (b * c)) → ((a → b) * (a → c))
*/
