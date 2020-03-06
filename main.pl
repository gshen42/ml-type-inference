:- set_prolog_flag(occurs_check, true).

:- op(700, xfy, →).
:- op(900, xfx, :).
:- op(910, xfx, ⊢).
:- op(920, xfx, ∈).
:- op(300, yfx, $).

% ∈ finds the first binding in the context
X ∈ [X | _] :- !.
X ∈ [_ | L] :- X ∈ L.

/* STLC */

Γ ⊢ var(X) : Ty :-
    (X:Ty) ∈ Γ, !.

Γ ⊢ lam(X, T2) : Ty1 → Ty2 :-
    [X:Ty1 | Γ] ⊢ T2 : Ty2.

Γ ⊢ T1 $ T2 : Ty2 :-
    Γ ⊢ T1 : Ty1 → Ty2,
    Γ ⊢ T2 : Ty1.

/*
Examples:

term:  λx. x
query: [] ⊢ lam(x, var(x)) : Ty.

term:  λf. λx. f (f x)
query: [] ⊢ lam(f, lam(x, var(f) $ (var(f) $ var(x)))) : Ty.
*/

/* Unit Type */

Γ ⊢ unit : tyUnit.

/*
Examples:

term: unit
query: [] ⊢ unit : Ty.

term: λx. unit
query: [] ⊢ lam(x, unit) : Ty.
*/

/* Ascription */

Γ ⊢ as(T, Ty) : Ty :-
    Γ ⊢ T : Ty.

/*
Examples:

term: λx. x as A
query: [] ⊢ lam(x, as(var(x), a)) : Ty.

term: (λx. x) as (A → A)
query: [] ⊢ as(lam(x, var(x)), a → a) : Ty.
*/

/* Product Types */

Γ ⊢ {T1, T2} : Ty1 * Ty2 :-
    Γ ⊢ T1 : Ty1,
    Γ ⊢ T2 : Ty2.

Γ ⊢ fst(T) : Ty1 :-
    Γ ⊢ T : Ty1 * Ty2.

Γ ⊢ snd(T) : Ty2 :-
    Γ ⊢ T : Ty1 * Ty2.

/*
Examples:

term: λx. fst t
query: [] ⊢ lam(x, fst(var(x))) : Ty.

term: λx. fst (snd t)
query: [] ⊢ lam(x, fst(snd(var(x)))) : Ty.
*/

/* Sum Type */

Γ ⊢ inl(T) : Ty1 + Ty2 :-
    Γ ⊢ T : Ty1.

Γ ⊢ inr(T) : Ty1 + Ty2 :-
    Γ ⊢ T : Ty2.

Γ ⊢ case(T, X1, T1, X2, T2) : Ty :-
    Γ ⊢ T : Ty1 + Ty2,
    [(X1:Ty1)| Γ] ⊢ T1 : Ty,
    [(X2:Ty2)| Γ] ⊢ T2 : Ty.

/*
Examples:

term: λx. inr x.
query: [] ⊢ lam(x, inr(var(x))) : Ty.

term: λx. case x of inl(t1) -> t1 unit
                    inr(t2) -> snd t2
query: [] ⊢ lam(x, case(var(x), t1, var(t1) $ unit, t2, snd(var(t2)))) : Ty.
*/

/* Fix */

Γ ⊢ fix(T) : Ty :-
    Γ ⊢ T : Ty → Ty.

/*
Examples:

term: fix (λf. λx. f x)
query: [] ⊢ fix(lam(f, lam(x, var(f) $ var(x)))) : Ty.

term: fix (λf. f)
query: [] ⊢ fix(lam(f, var(f))) : Ty.
*/

/* Booleans */

Γ ⊢ true : tyBool.

Γ ⊢ false : tyBool.

Γ ⊢ not(T1) : tyBool :-
    Γ ⊢ T1 : tyBool.

Γ ⊢ and(T1, T2) : tyBool :-
    Γ ⊢ T1 : tyBool,
    Γ ⊢ T2 : tyBool.

Γ ⊢ if(T1, T2, T3) : Ty :-
    Γ ⊢ T1 : tyBool,
    Γ ⊢ T2 : Ty,
    Γ ⊢ T3 : Ty.

/*
Examples:

term: true && false
query: [] ⊢  and(true, false) : Ty.

term: λx. if (fst x) then (snd x) else unit
query: [] ⊢ lam(x, if(fst(var(x)), snd(var(x)), unit)) : Ty.
*/

/* Let Polymorphism */

Γ ⊢ var(X) : Ty :-
    poly(X:T) ∈ Γ,
    Γ ⊢ T : Ty.

Γ ⊢ let(X, T1, T2) : Ty2 :-
    Γ ⊢ T1 : Ty1,
    [poly(X:T1) | Γ] ⊢ T2 : Ty2.

/*
Examples:

term: let id = λx. x in
      id true
query: [] ⊢ let(id, lam(x, var(x)), var(id) $ true) : Ty.

term: let id = λx. x in
      let a = id true in
      let b = id unit in
      unit
query: [] ⊢ let(id, lam(x, var(x)), let(a, var(id) $ true, let(b, var(id) $ unit, unit))) : Ty.
*/
