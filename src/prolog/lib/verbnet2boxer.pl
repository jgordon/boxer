
/* ========================================================================
   File Search Paths
=========================================================================*/

file_search_path(semlib,     'src/prolog/lib').
file_search_path(boxer,      'src/prolog/boxer').
file_search_path(knowledge,  'src/prolog/boxer/knowledge').
file_search_path(lex,        'src/prolog/boxer/lex').


/* ========================================================================
   VerbNet
=========================================================================*/

:- dynamic verbnet/3.


/* ========================================================================
   Modules
=========================================================================*/

:- use_module(library(lists),[member/2]).
:- use_module(boxer(slashes)).


/* ========================================================================
   Main
=========================================================================*/

verbnet2prolog(File):- 
   load_xml_file(File,T), 
%  pretty_print(T,0),
   elements(T,['VNCLASS'],f(X,C)),   
   value(X,'ID',ID),
   members(C,File,ID,_).


/* ----------------------------------------------------------------------
   Pretty Printing XML
---------------------------------------------------------------------- */ 

pretty_print([],_).

pretty_print([element(A,B,C)|L],Tab):- !,
   tab(Tab), write(A), write(' '), write(B), nl,
   NewTab is Tab+3, 
   pretty_print(C,NewTab),
   pretty_print(L,Tab).

pretty_print([E|L],Tab):-  
   tab(Tab), write(unknown:E),nl,
   pretty_print(L,Tab).


/* ----------------------------------------------------------------------
   Processing all members of a VerbNet class
---------------------------------------------------------------------- */ 

members(X,File,XID,Names):-
   findall(Sub:YID,(elements(X,['SUBCLASSES','VNSUBCLASS'],f(Y,Sub)),value(Y,'ID',YID)),Subs),
   subclasses(Subs,File,Names1),
   findall(Frame,(elements(X,['FRAMES','FRAME'],f(_,Frame))),Frames),
   findall(Name,(elements(X,['MEMBERS','MEMBER'],f(Member,_)),value(Member,name,Name)),Names2),
   append(Names1,Names2,Names),
   frames(Frames,Names,XID,File).


/* ----------------------------------------------------------------------
   Processing all subclasses of a VerbNet class
---------------------------------------------------------------------- */ 

subclasses([],_,[]).

subclasses([X:XID|L],File,Names):-
   members(X,File,XID,Names1),
   append(Names1,Names2,Names),
   subclasses(L,File,Names2).


/* ----------------------------------------------------------------------
   Process frames
---------------------------------------------------------------------- */ 

frames([],_,_,_):- !.

frames([Frame|L],Names,ID,File):-
   elements(Frame,['DESCRIPTION'],f(De,_)),   
   value(De,primary,Primary),
   example(Frame,Example),
   elements(Frame,['SYNTAX'],f(_,Syntax)),  
   subcat(Syntax,[],SubCat), 
   reverse(SubCat,Normal),
   ccg(SubCat,C^C,CCG,Missing,Roles),
   atom_chars(ID,IDChars),
   formatID(IDChars,[_,_|FID]),
   format('~n%%% File:    ~p~n%%% Primary: ~p (~p)~n%%% Syntax:  ~p~n',[File,Primary,ID,Normal]),
   write('%%% CCG:     '), write(CCG), 
   format('~n%%% Roles:   ~p~n',[Roles]),
   ( Missing = [], !; format('%%% Missing: ~p~n',[Missing]) ),
   format('%%% Example: ~p~n%%%~n',[Example]),
   frameMembers(Names,CCG,FID,Roles),
   frames(L,Names,ID,File).


/* ----------------------------------------------------------------------
   Check if there is an example for a frame
---------------------------------------------------------------------- */ 

example(Frame,Example):-
   elements(Frame,['EXAMPLES','EXAMPLE'],f(_,[Example])), !.

example(_,'error (no example)').  


/* ----------------------------------------------------------------------
   Process all members of a frame
---------------------------------------------------------------------- */ 

frameMembers([],_,_,_).

frameMembers([Name1|L],CCG,FID,Roles):-
   reformatName(Name1,Name2),
   format('verbnet(~q, ',[Name2]),
   write(CCG),
   format(', ~q, ~q).~n',[Roles,FID]),
   add(CCG,Roles),
   frameMembers(L,CCG,FID,Roles).


/* ----------------------------------------------------------------------
   Reformat Verbnet names (underscores for spaces)
---------------------------------------------------------------------- */ 

reformatName(N1,N2):-
   atom_chars(N1,C1),
   reformatString(C1,C2),
   atom_chars(N2,C2).

reformatString([],[]).
reformatString([' '|L1],['_'|L2]):- !, reformatString(L1,L2).
reformatString([C|L1],[C|L2]):- reformatString(L1,L2).


/* ----------------------------------------------------------------------
   Add entries to Prolog database
---------------------------------------------------------------------- */ 

add(CCG,Roles):-
   verbnet(CCG,Roles,Old), !,
   New is Old + 1,
   retract(verbnet(CCG,Roles,Old)),
   assert(verbnet(CCG,Roles,New)).

add(CCG,Roles):-
   assert(verbnet(CCG,Roles,1)).


/* ----------------------------------------------------------------------
   Format VerbNet ID
---------------------------------------------------------------------- */ 

formatID(Chars,[Pre,Sep1|L]):-
   Seps = ['-','.'], member(Sep1,Seps),
   append(PreChars,[Sep1|RestChars],Chars), 
   \+ ( member(Sep2,Seps), member(Sep2,PreChars) ), !,
   formatNumber(PreChars,Pre),
   formatID(RestChars,L).

formatID(Chars,[ID]):-
   formatNumber(Chars,ID).

formatNumber(Chars,Num):-
   Chars = [First|_], 
   member(First,['0','1','2','3','4','5','6','7','8','9']), !, 
   number_chars(Num,Chars).

formatNumber(Chars,Atom):-
   atom_chars(Atom,Chars).

/* ----------------------------------------------------------------------
   Printing the subcat frame
---------------------------------------------------------------------- */ 

subcat([],Acc,Acc).
subcat([E|L],Acc1,Acc3):- cat(E,Acc1,Acc2), subcat(L,Acc2,Acc3).


/* ----------------------------------------------------------------------
   Constructing CCG category
---------------------------------------------------------------------- */ 

% terminating
%
ccg([np:_,pp],X^C,C,[],[]):- !, X=pp.
ccg([np:_,prep:_],X^C,C,[],[]):- !, X=pp.
ccg([np:R],np^C,C,[],[R]):- !.
ccg([s:R],(s:'_')^C,C,[],[R]):- !.
ccg([pp:_],pp^C,C,[],[]):- !.
ccg([X],X^C,C,[],[]):- !.

% recursive
%
ccg([np:_,prep:_|L],X^Old,New,M,Roles):- !, ccg(L,X^(Old/pp),New,M,Roles).
ccg([np:_,pp|L],X^Old,New,M,Roles):- !, ccg(L,X^(Old/pp),New,M,Roles).
ccg([np:R|L],X^Old,New,M,[R|Oles]):- !, ccg(L,X^(Old/np),New,M,Oles).
ccg([s_to:R|L],X^Old,New,M,[R|Oles]):- !, ccg(L,X^(Old/(s:to\np)),New,M,Oles).
ccg([s_ng:R|L],X^Old,New,M,[R|Oles]):- !, ccg(L,X^(Old/(s:ng\np)),New,M,Oles).
ccg([s:R|L],X^Old,New,M,[R|Oles]):- !, ccg(L,X^(Old/s:'_'),New,M,Oles).
ccg([v|L],X^Old,New,M,Roles):- !, X=(s:'_'\Y), ccg(L,Y^Old,New,M,Roles).
ccg([adv|L],Old,New,M,Roles):- !, ccg(L,Old,New,M,Roles).
%ccg([lex:(\'s)|L],Old,New,M,Roles):- !, ccg(L,Old,New,M,Roles).  %%% not always correct!
ccg([U|L],Old,New,[U|M],Roles):- !, ccg(L,Old,New,M,Roles).


/* ----------------------------------------------------------------------
   Syntactic Restrictions
---------------------------------------------------------------------- */ 

restr(Restr,Type):- 
  Restr = [element('SYNRESTRS',[],L)],
  member(element('SYNRESTR',['Value'='+',type=Type],[]),L), !.

s_restr(that_comp).
s_restr(for_comp).
s_restr(wh_comp).

% s_restr(poss_ing). % not sentence!
s_restr(acc_ing).
s_restr(oc_ing).
s_restr(ac_ing).
s_restr(be_sc_ing).
s_restr(np_omit_ing).  % ???
s_restr(np_ppart).     % ??? 
s_restr(np_p_ing).     % ???
s_restr(np_ing).       % ???

s_restr(how_extract).
s_restr(what_extract).

s_restr(wh_inf).
s_restr(what_inf).
s_restr(wheth_inf).
s_restr(oc_bare_inf).
s_restr(oc_to_inf).
s_restr(ac_to_inf).
s_restr(sc_to_inf).
s_restr(np_to_inf).
s_restr(vc_to_inf).
s_restr(rs_to_inf). % very rare -- bug?
s_restr(to_inf_rs). % very rare -- bug?


/* ----------------------------------------------------------------------
   Printing a category
---------------------------------------------------------------------- */ 

cat(element('NP', [value=Value], R),A,[s_ng:Value|A]):- restr(R,ac_ing), !.
cat(element('NP', [value=Value], R),A,[s_to:Value|A]):- restr(R,sc_to_inf), !.
cat(element('NP', [value=Value], R),A,[s:Value|A]):- s_restr(S), restr(R,S), !.
cat(element('NP', [value=Value], _),A,[np:Value|A]):- !.
cat(element('PREP', [], _),A,[pp|A]):- !.
cat(element('PREP', [value=Value], _),A,[prep:Value|A]):- !.
cat(element('LEX', [value='[+be]'], _),A,[lex:be|A]):- !. 
cat(element('LEX', [value='it[+be]'], _),A,[lex:be,lex:it|A]):- !.
cat(element('LEX', [value=at], _),A,[prep:at|A]):- !.
cat(element('LEX', [value=of], _),A,[prep:of|A]):- !.
cat(element('LEX', [value=Value], _),A,[lex:Value|A]):- !.
cat(element('VERB',[],[]),A,[v|A]):- !.
cat(element('ADJ',[],[]),A,[adj|A]):- !.
cat(element('ADV',[],[]),A,[adv|A]):- !.
cat(U,A,[unk:U|A]):- !.


/* ----------------------------------------------------------------------
   Processing elements of the XML tree
---------------------------------------------------------------------- */ 

elements([element(X,F,L)|_],[X],f(F,L)).
elements([element(X,_,L)|_],[X|R],A):- elements(L,R,A).
elements([_|L],X,A):- elements(L,X,A).


/* ----------------------------------------------------------------------
   Accessing a value
---------------------------------------------------------------------- */ 

value([Name=Value|_],Name,Value):- !.
value([_|L],Name,Value):- value(L,Name,Value).


/* ----------------------------------------------------------------------
   VerbNet Directory
---------------------------------------------------------------------- */ 

verbnet_dir('ext/VerbNet/').


/* ----------------------------------------------------------------------
   Processing all XML files
---------------------------------------------------------------------- */ 

process([]):- planB.

process([File|L]):-
   verbnet2prolog(File), !,
   process(L).

planB:- 
   setof(X,A^B^verbnet(X,A,B),L), 
   format('~n%%% Most frequent roles for a particular CCG category.~n%%%~n',[]),
   format('verbnet(_, ~p, [~q], []). % ~n',[s:adj\np,'Topic']),
   planB(L).

planB([]).

planB([CCG|L]):-
   verbnet(CCG,R,N), \+ (verbnet(CCG,_,M), M>N),
   write('verbnet(_, '), 
   write(CCG), 
   format(' , ~q, []). % n=~p~n',[R,N]), 
   planB(L).

/* ----------------------------------------------------------------------
   Header
---------------------------------------------------------------------- */ 

header:-
   format('%%% automatically generated by src/prolog/lib/verbnet2boxer.pl~n%%%~n',[]),
   format(':- module(verbnet,[verbnet/3,verbnet/4]).~n',[]),
   format(':- use_module(boxer(slashes)).~n~n',[]),
   format('%%% wrapper~n%%%~nverbnet(A,B,C):- verbnet(A,B,C,_).~n').


/* ----------------------------------------------------------------------
   Wildcard for XML files to be processed
---------------------------------------------------------------------- */ 

wildCard('*.xml').
%wildCard('put-9.1.xml').
%wildCard('matter-91.xml').
%wildCard('run-51.3.2.xml').
%wildCard('adjust-26.9.xml').
%wildCard('amalgamate-22.2.xml').


/* ----------------------------------------------------------------------
   Start Predicate
---------------------------------------------------------------------- */ 

run:- 
   verbnet_dir(Dir), 
   exists_directory(Dir),
   wildCard(WildCard),
   atom_concat(Dir,WildCard,Expand),
   expand_file_name(Expand,Files),
   header,
   process(Files), 
   halt.

:- run.
