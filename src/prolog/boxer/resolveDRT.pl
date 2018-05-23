
:- module(resolveDRT,[resolveDrs/1,goldAntecedent/2]).

:- use_module(boxer(bindingViolation),[noBindingViolationDrs/1]).
:- use_module(boxer(freeVarCheck),[boundVarCheckContext/2,drsCondition/2]).
:- use_module(library(lists),[member/2,append/3,select/3]).
:- use_module(semlib(options),[option/2]).
:- use_module(semlib(errors),[warning/2]).
:- use_module(boxer(categories),[att/3]).


/* ========================================================================
   Dynamic Predicate
======================================================================== */

:- dynamic antecedent/2.


/* ========================================================================
   Managing Gold Standard Antecedents
======================================================================== */

goldAntecedent(Index,Att):-
   att(Att,antecedent,Antecedent), 
   number(Antecedent), !,
%  write(antecedent(Index,Antecedent)),nl,
   assert(antecedent(Index,Antecedent)).

goldAntecedent(_,_).


/* ========================================================================
   Main predicate: resolveDrs/1
======================================================================== */

resolveDrs(B):- option('--resolve',true), !, resolveDRS(B,[]-_,[]-_).
resolveDrs(_).


/* ========================================================================
   Main predicate: resolveDRS/3 (DRS)

   Context is a diffrerence list of pointed DRSs (i.e. a projection
   path), ordered on recency (closest first).
======================================================================== */

resolveDRS(sdrs([],_),C-C,P-P):- !.

resolveDRS(sdrs([lab(_,B)|L],C),C1-C3,P1-P3):- !,
   resolveDRS(B,C1-C2,P1-P2),
   resolveDRS(sdrs(L,C),C2-C3,P2-P3).

resolveDRS(sdrs([sub(B1,B2)|L],C),C1-C3,P1-P4):- !,
   resolveDRS(B1,C1-C2,P1-P2),
   resolveDRS(B2,C2-_,P2-P3),
   resolveDRS(sdrs(L,C),C2-C3,P3-P4).

resolveDRS(merge(B1,B2),C1-C3,P1-P3):- !,
   resolveDRS(B1,C1-C2,P1-P2),
   resolveDRS(B2,C2-C3,P2-P3).

resolveDRS(lab(_,B),Context,P):- !,
   resolveDRS(B,Context,P).

resolveDRS(K:B,C1-C2,P1-P3):-
   anaphoric(K:B,ADRS,C1,P1), !,                            %%% if there is a free pointer
   project([K:B|C1],ADRS,P1,P1-P2,[K:B|C1],[]),             %%% then resolve it
   resolveDRS(K:B,C1-C2,P2-P3).

resolveDRS(K:drs(D,C),C1-[K:drs(D,C)|C1],P):- !,
   resolveConds(C,[K:drs(D,C)|C1],P).

resolveDRS(U,C-C,P-P):- 
   warning('unknown DRS in resolveDRS/3: ~p',[U]).


/* ========================================================================
   Resolve Conditions
======================================================================== */

resolveConds([],_,P-P):- !.

resolveConds([_:C|L],Context,P):- !, 
   resolveConds([C|L],Context,P).

resolveConds([not(B)|C],Context,P1-P3):- !,
   resolveDRS(B,Context-_,P1-P2),
   resolveConds(C,Context,P2-P3).

resolveConds([nec(B)|C],Context,P):- !,
   resolveConds([not(B)|C],Context,P).

resolveConds([pos(B)|C],Context,P):- !,
   resolveConds([not(B)|C],Context,P).

resolveConds([prop(_,B)|C],Context,P):- !,
   resolveConds([not(B)|C],Context,P).

resolveConds([imp(B1,B2)|C],C1,P1-P4):- !,
   resolveDRS(B1,C1-C2,P1-P2),
   resolveDRS(B2,C2-_,P2-P3),
   resolveConds(C,C1,P3-P4).

resolveConds([duplex(_,B1,_,B2)|C],Context,P):- !,
   resolveConds([imp(B1,B2)|C],Context,P).

resolveConds([or(B1,B2)|C],C1,P1-P4):- !,
   resolveDRS(B1,C1-_,P1-P2),
   resolveDRS(B2,C1-_,P2-P3),
   resolveConds(C,C1,P3-P4).

resolveConds([_|C],Context,P):- !,
   resolveConds(C,Context,P).


/* ========================================================================
   Identify Anaphoric Material (free pointers)

   K1 = K2:X K3:Y
        K2:dog(X,Y)
        K3:male(Y)
        K1:walks(X)
======================================================================== */

anaphoric(P:drs(PDom,PCon),F:drs(FDom,FCon),Context,Presups):-
   member(F:_:_,PDom), \+ P==F,       % pick a free pointer (of DRS domain) 
   \+ (member(K:_,Context), K==F),    % should not be in context (that would mean it is resolved already)
   \+ (member(K:_,Presups), K==F),    % should not be in presuppositions (would mean it's resolved already)
   anaphoricSet(PDom,F,FDom),
   anaphoricSet(PCon,F,FCon),
   noFreeVars(FCon,P,PDom), !.


/* ========================================================================
   Check for bound variable
======================================================================== */

boundVar(X,P1,Dom):-
   member(P2:_:Y,Dom), 
   X==Y, !, \+ P1==P2.
  
boundVar(_,_,_).


/* ========================================================================
   Check if there are no free variables
======================================================================== */

noFreeVars([],_,_).

noFreeVars([F:_:rel(X,Y,_,_)|L],P,Dom):- !,
   (boundVar(X,P,Dom);boundVar(X,F,Dom)),
   (boundVar(Y,P,Dom);boundVar(Y,F,Dom)),
   noFreeVars(L,P,Dom).

noFreeVars([_|L],P,Dom):- !,
  noFreeVars(L,P,Dom).


/* ========================================================================
   Compute Anaphoric Material
======================================================================== */

anaphoricSet([],_,[]).
anaphoricSet([P:E|L1],F,[P:E|L2]):- P==F, !, anaphoricSet(L1,F,L2).
anaphoricSet([_|L1],F,L2):- anaphoricSet(L1,F,L2).


/* ========================================================================
   Projection -- try to bind, else accommodate

   project(+List of Context DRSs (Possible antecedents),
           +Anaphoric DRS,
           +List of presuppositions seen so far (could act as antecedents),
           +Pair of Ingoing and Output List of Presuppositions
           +List of DRSs (local DRS + context DRS, to check for binding violations)
           -Accumulator of solution/4)
======================================================================== */

% No further context DRSs, no presupposed DRSs, but earlier binding
% solutions; so pick most probable solution
%
project([],B,[],P1-P2,Bs,Solutions):-                          % Tried all possibilities
   sort([solution(0.94,_,_,free)|Solutions],Sorted),           % Sort on score
   best(Sorted,Bs,B,P1-P2), !.

% No further context DRSs, try a presupposed DRSs as antecedent
%
project([],K2:B2,[K1:drs([K0:_:X|D],C)|P],P1-P2,Bs,Solutions):-
   K1==K0,                                 % Antecedent DRS from context
   match(K1,C,X,B2,Y,Score,Ant), !,        % Match antecedent with anaphoric DRS
   project([],K2:B2,[K1:drs(D,C)|P],P1-P2,Bs,[solution(Score,K1:X,K2:Y,Ant)|Solutions]).

% No further context DRSs, try accommodation in presupposition
%
project([],K2:B2,[K1:drs([],_)|P],P1-P2,Bs,Solutions):- !,
   project([],K2:B2,P,P1-P2,Bs,[solution(0.91,K1:_,K2:_,global)|Solutions]).

% Try next presupposed DRS
%
project([],K,[_|P],P1-P2,Bs,Solutions):- !,
   project([],K,P,P1-P2,Bs,Solutions).

% Match antecedent with anaphoric DRS
% Look in same DRS for other antecedent
% 
project([K1:drs([K0:_:X|D],C)|Context],K2:B2,P,P1-P2,Bs,Solutions):-      
   K1==K0,
   match(K1,C,X,B2,Y,Score,Source), !,
   project([K1:drs(D,C)|Context],K2:B2,P,P1-P2,Bs,[solution(Score,K1:X,K2:Y,Source)|Solutions]).

% Try next discourse referent
%
project([K1:drs([_|D],C)|Context],A,P,P1-P2,Bs,Solutions):- !,
   project([K1:drs(D,C)|Context],A,P,P1-P2,Bs,Solutions).

% Tried all discourse referents, accommodate (non-global)
% and go on with next context DRS
%
project([K1:drs([],_)|Context],K2:B2,P,P1-P2,Bs,Solutions):- !,
   length(Context,Levels), Prob is 0.05/(Levels + 1),
   Score is 1-Prob,
   project(Context,K2:B2,P,P1-P2,Bs,[solution(Score,K1:_,K2:_,local)|Solutions]).

% Try next context DRS (all other cases)
%
project([_|Context],A,P,P1-P2,Bs,Solutions):- !,  % first argument can be an SDRS?
   project(Context,A,P,P1-P2,Bs,Solutions).


/* ========================================================================
   Best (sorted on score, the lower the better!)
======================================================================== */   

best([Solution|_],Bs,ADRS,P-[ADRS|P]):- 
   Solution = solution(_Score,_,_,free),
   append(Bs,[ADRS|P],Context),
   boundVarCheckContext(Context,ADRS), !.

best([Solution|_],Bs,ADRS,P-P):- 
   Solution = solution(_Score,X,Y,Reason),
   member(Reason,[local,global]),
   append(Bs,P,Context),
   \+ \+ (X=Y, boundVarCheckContext(Context,ADRS)), !, 
   X=Y.

best([Solution|_],Bs,ADRS,P-P):- 
   Solution = solution(_Score,X,Y,Reason),
   \+ member(Reason,[local,global,free]),
   append(Bs,P,Context),
   \+ \+ (X=Y, 
          boundVarCheckContext(Context,ADRS), 
          noBindingViolationDrs(Bs)), !, 
   X=Y.

best([_|L],Bs,ADRS,P):- best(L,Bs,ADRS,P).


/* ========================================================================
   Match antecedent with presupposition

   match(+Label of Antecedent DRS,
         +Conditions of Antecedent DRS,
         +Referent of Antecedent DRS,
         +Unlabeled Anaphoric DRS,
         -Referent of Anaphoric DRS,
         -Matching Score,
         -Matching Type)

======================================================================== */   

match(K1,C1,X,drs([_:_:Y|_],C2),Y,0,bow):-
   antecedent(I2,AntInd),           % there is a gold antecedent
   member( _:I2:_,C2),              % for the current anaphoric expression
   member(K2:I1:Ant,C1), K1==K2,    % and the antecedent is part of the 
   member(AntInd,I1), !,            % DRS under consideration
   drsCondition(Z,Ant),
   Z==X.
 
match(K1,C1,X,drs(_,C2),Y,NewScore,P):-
   member( _:_:Ana,C2),
   member(K2:_:Ant,C1), K1==K2, 
   matching(Y^Ana,Z^Ant,Score,P), Z==X,
   NewScore is 1-Score,
   noconflicts(Y,C2,X,C1), !.


/* ========================================================================
   Check for Conflicts
======================================================================== */   

noconflicts(X,_,Y,C2):-                            %%% resolving should
    \+ \+ ( X=Y,                                   %%% not result in X=X
            \+ ( member(_:_:not(_:drs(_,C0)),C2),  %%% in a negated DRS
                 member(_:_:eq(A,B),C0),
                 A==X, B==X ) ).


/* ========================================================================
   Matching (anaphor, antecedent)
======================================================================== */   

% time
matching(Y^pred(Y,now,a,1),Z^pred(Z,now,a,1),0.99,a:now).

% he
matching(Y^pred(Y,male,n,2),Z^named(Z,S,per,_),0.9,per:S).
matching(Y^pred(Y,male,n,2),Z^named(Z,S,_,_),0.1,per:S).
matching(Y^pred(Y,male,n,2),Z^pred(Z,male,n,2),0.99,n:male).
matching(Y^pred(Y,male,n,2),Z^pred(Z,S,n,_),0.5,n:S):-  option('--x',false).
matching(Y^pred(Y,male,n,2),Z^card(Z,_,_),0.1,card):- option('--x',false).

% she
matching(Y^pred(Y,female,n,2),Z^named(Z,S,per,_),0.9,per:S).
matching(Y^pred(Y,female,n,2),Z^named(Z,S,_,_),0.1,per:S).
matching(Y^pred(Y,female,n,2),Z^pred(Z,female,n,2),0.99,n:female).
matching(Y^pred(Y,female,n,2),Z^pred(Z,S,n,_),0.5,n:S):-  option('--x',false).
matching(Y^pred(Y,female,n,2),Z^card(Z,_,_),0.1,card):- option('--x',false).

% it
matching(Y^pred(Y,neuter,a,_),Z^named(Z,S,per,_),0.1,per:S).
matching(Y^pred(Y,neuter,a,_),Z^named(Z,S,_,_),0.8,per:S).
matching(Y^pred(Y,neuter,a,_),Z^pred(Z,neuter,a,_),0.99,a:neuter).
matching(Y^pred(Y,neuter,a,_),Z^pred(Z,S,n,_),0.5,n:S).

% they, them, theirs, this, that, those, these
matching(Y^pred(Y,thing,n,12),Z^pred(Z,S,n,_),0.5,n:S):-  option('--x',false).
matching(Y^pred(Y,thing,n,12),Z^named(Z,S,_,_),0.1,per:S):- option('--x',false).

% I, me, mine, you, yours, we, us, ours, myself, yourself, ourselves
matching(Y^pred(Y,person,n,1),Z^pred(Z,S,n,_),0.1,n:S):-    option('--x',false).
matching(Y^pred(Y,person,n,1),Z^named(Z,S,per,_),0.8,per:S):- option('--x',false).
matching(Y^pred(Y,person,n,1),Z^named(Z,S,_,_),0.5,per:S):-   option('--x',false).

% the
matching(Y^pred(Y,S,n,_),Z^pred(Z,S,n,_),0.9,n:S).

% names
matching(Y^named(Y,S,T,_),Z^named(Z,S,T,_),0.9,per:S).
matching(Y^named(Y,S,_,_),Z^named(Z,S,_,_),0.7,per:S).

% timex
matching(Y^timex(Y,date(_:D1,_:D2,_:D3,_:D4)),Z^timex(Z,date(_:D1,_:D2,_:D3,_:D4)),0.9,timex).
