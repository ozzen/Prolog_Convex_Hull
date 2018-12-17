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

%XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX%

%GRAHAM SCAN

% takes a collection of points as input
:-['points.txt'].

% pushing all points in a list
lowest(T) :- findall(Y, points(Z,X,Y), T).
leftmost(T) :- findall(X, newpoints(Z,X,Y), T).

% calculating the lowest and the leftmost point
left_min(X) :- leftmost(T),			   
		list_min(T,X).
low_min(X) :- lowest(T), 
	       list_min(T,X).

% Calculating minimum in a list.
list_min([L|Ls], Min) :- list_min(Ls, L, Min).
list_min([], Min, Min).
list_min([L|Ls], Min0, Min) :- Min1 is min(L, Min0),
				list_min(Ls, Min1, Min).
				
% Obtaining final starting point, guaranteed to be on convex hull.
newpoints(Z,X,Y) :- low_min(Y), 
		     points(Z,X,Y).
lowest_leftmost(Z,X,Y) :- left_min(X), 
			   newpoints(Z,X,Y).

% Sorting based on angle.
angle(T,C) :- lowest_leftmost(Z,X,Y), 
		points(C,A,B), 
		T is atan2((B-Y),(A-X))*(180/pi), 
		Z\=C.
prepsort(T-C) :- angle(T,C).
finalsort(R) :- findall(C,prepsort(C),C), 
		 keysort(C,R).

% checking whether the next point lies on the convex hull or not
check_dir(X1,Y1,X2,Y2,X3,Y3,Z) :- Z is ((X2-X1)*(Y3-Y1))-((Y2-Y1)*(X3-X1)).

% selecting the three points to make comparison
choose_three_points([],L).
choose_three_points(Z,L,R) :- finalsort(Z), 
			       points(Z,X,Y), 
			       nextto(L,R,[L,R|Z]).
			       
graham_scan(Z,X,Y) :- lowest_leftmost(Z,X,Y).
graham_scan(Z,X,Y) :- choose_three_points(Z,L,R),
			{check_dir(X1,Y1,X2,Y2,X3,Y3,D), 
			>=(D,0)
			-> 
			graham_scan(Z3,X3,Y3)
			; 
			graham_scan(Z1,X1,Y1)}.
			

