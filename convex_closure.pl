% CONVEX CLOSURE

%project(+Xs,+Cxs,-ProjectCxs)

%preconditions:
% Xs is a closed list with distinct variables as elements
% Cxs is a closed list of linear constraints
% Cxs is satisfiable

%postconditions:
% Xs is a closed list with distinct variables as elements
% ProjectCxs is a closed list of linear constraints
% vars(ProjectCxs) ⊆ vars(Xs)
% P_Cxs,Xs = P_ProjectCxs,Xs

%-------------------------------------------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------------------------------------------%

:- use_module(library(clpq)).

project(Xs, Cxs, ProjectCxs) :- call_residue_vars(copy_term(Xs-Cxs, CpyXs-CpyCxs), _), 
				 tell_cs(CpyCxs), 
				 prepare_dump(CpyXs, Xs, Zs, DumpCxs, ProjectCxs), 
				 dump(Zs, Vs, DumpCxs), Xs = Vs.

prepare_dump([], [], [], Cs, Cs).
prepare_dump([X|Xs], YsIn, ZsOut, CsIn, CsOut) :- (ground(X) -> YsIn  = [Y|Ys], ZsOut = [_|Zs], CsOut = [Y=X|Cs] ;
         					   YsIn  = [_|Ys], ZsOut = [X|Zs], CsOut = Cs),
					           prepare_dump(Xs, Ys, Zs, CsIn, Cs).

tell_cs([]).
tell_cs([C|Cs]) :- {C}, tell_cs(Cs).

%++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++%
%++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++%

% CONVEX HULL CODE

%convex hull(+Xs, +Cxs, +Ys, +Cys, -Zs, -Czs)

%preconditions:
% Xs is a closed list with distinct variables as elements and likewise for Ys
% Xs and Ys have the same length
% vars(Xs) ∩ vars(Ys) = ∅
% Cxs and Cys are closed lists of linear constraints
% Cxs and Cys are both satisfiable
% vars(Cxs) ⊆ vars(Xs) and vars(Cys) ⊆ vars(Ys)

%postconditions:
% Xs, Ys and Zs are closed lists with distinct variables as elements
% Zs is the same length as both Xs and Ys
% Czs is a closed list of linear constraints
% vars(Czs) ⊆ vars(Zs) and (vars(Xs) ∪ vars(Ys)) ∩ vars(Zs) = ∅
% P_Czs,Zs is the closure of the convex hull of P_Cxs,Xs ∪ P_Cys,Ys 

%-------------------------------------------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------------------------------------------%

convex_hull(Xs, Cxs, Ys, Cys, Zs, Czs) :- scale(Cxs, Sig1, [], C1s), 
					   scale(Cys, Sig2, C1s, C2s),
 					   add_vect(Xs, Ys, Zs, C2s, C3s),
					   project(Zs, [Sig1 >= 0, Sig2 >= 0, Sig1+Sig2 = 1|C3s], Czs).

scale([], _, Cs, Cs).
scale([C1|C1s], Sig, C2s, C3s) :- C1 =.. [RelOp, A1, B1],		
			           C2 =.. [RelOp, A2, B2], 
				   mul_exp(A1, Sig, A2),
        			   mul_exp(B1, Sig, B2),
        			   scale(C1s, Sig, [C2|C2s], C3s).

mul_exp(E1, Sigma, E2) :- once(mulexp(E1, Sigma, E2)).
               
mulexp(X,_,X) :- var(X).
mulexp(N*X,_,N*X) :- ground(N), var(X).
mulexp(-X,Sig,-Y) :- mulexp(X, Sig, Y).
mulexp(A+B, Sig,C+D) :- mulexp(A, Sig, C), mulexp(B, Sig, D).
mulexp(A-B, Sig,C-D) :- mulexp(A, Sig, C), mulexp(B, Sig, D).
mulexp(  N, Sig, N*Sig) :- ground(N).

add_vect([], [], [], Cs, Cs).
add_vect([U|Us], [V|Vs], [W|Ws], C1s, C2s) :- add_vect(Us, Vs, Ws, [W = U+V|C1s], C2s).



