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

term: λx. fst x
query: [] ⊢ lam(x, fst(var(x))) : Ty.

term: λx. fst (snd x)
query: [] ⊢ lam(x, fst(snd(var(x)))) : Ty.
*/

/* Sum Types */

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

Γ ⊢ or(T1, T2) : tyBool :-
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

/* Natural Numbers */

Γ ⊢ 0 : tyNat.

Γ ⊢ succ(T) : tyNat :-
    Γ ⊢ T : tyNat.

Γ ⊢ T1 + T2 : tyNat :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 - T2 : tyNat :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 * T2 : tyNat :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 / T2 : tyNat :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 == T2 : tyBool :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 > T2 : tyBool :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

Γ ⊢ T1 < T2 : tyBool :-
    Γ ⊢ T1 : tyNat,
    Γ ⊢ T2 : tyNat.

/* some shorthads for Natural Numbers */
Γ ⊢ 1 : tyNat.
Γ ⊢ 2 : tyNat.
Γ ⊢ 3 : tyNat.
Γ ⊢ 4 : tyNat.
Γ ⊢ 5 : tyNat.

/*
Examples:

term: fix lambda f. lambda x. if x < 0 || x == 0
                              then 1
                              else x * f (x - 1)
query: [] ⊢ fix(lam(f, lam(x, if(or(var(x)<0, var(x)==0), 1, var(x) * (var(f) $ (var(x) - 1)))))) : Ty.

term: fix lambda f. lambda x. if x < 0 || x == 0
                              then 0
                              else if x == 1
                                   then 1
                                   else f (x - 1) + f (x - 2)
query: [] ⊢ fix(lam(f, lam(x, if(or(var(x)<0, var(x)==0), 0, if(var(x)==1, 1, var(f) $ (var(x) - 1) + var(f) $ (var(x) - 2)))))) : Ty.
*/

/* Lists */

Γ ⊢ nil : tyList(Ty).

Γ ⊢ cons(T1, T2) : tyList(Ty) :-
    Γ ⊢ T1 : Ty,
    Γ ⊢ T2 : tyList(Ty).

Γ ⊢ isNil(T) : tyBool :-
    Γ ⊢ T : tyList(Ty).

Γ ⊢ head(T) : Ty :-
    Γ ⊢ T : tyList(Ty).

Γ ⊢ tail(T) : tyList(Ty) :-
    Γ ⊢ T : tyList(Ty).

/*
Examples:

term: [1,2,3,4,5]
query: [] ⊢ cons(1, cons(2, cons(3, cons(4, cons(5, nil))))) : Ty.

term: fix lambda self. lambda f. lambda l. if (isNil l)
                                           then nil
                                           else cons (f (head l)) (self f (tail l))
query: [] ⊢ fix(lam(self, lam(f, lam(l, if(isNil(var(l)), nil, cons(var(f) $ head(var(l)), var(self) $ var(f) $ tail(var(l)))))))) : Ty.
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
      let b = id 1 in
      2
query: [] ⊢ let(id, lam(x, var(x)), let(a, var(id) $ true, let(b, var(id) $ 1, 2))) : Ty.
*/
