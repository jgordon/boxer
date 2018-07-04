:- module(ne,[neClass/2,neClassType/3,neClassType/4]).

neClassType('I-LOC',loc,nam):- !.
neClassType('B-LOC',loc,nam):- !.
neClassType('E-LOC',loc,nam):- !.

neClassType('I-ORG',org,nam):- !.
neClassType('B-ORG',org,nam):- !.
neClassType('E-ORG',org,nam):- !.

neClassType('I-PER',per,nam):- !.
neClassType('B-PER',per,nam):- !.
neClassType('E-PER',per,nam):- !.

neClassType('I-DAT',tim,nam):- !.
neClassType('B-DAT',tim,nam):- !.
neClassType('E-DAT',tim,nam):- !.

neClassType('I-TIM',tim,nam):- !.
neClassType('B-TIM',tim,nam):- !.
neClassType('E-TIM',tim,nam):- !.

neClassType('I-MON',geo,nam,'UOM'):- !.
neClassType('B-MON',geo,nam,'UOM'):- !.
neClassType('E-MON',geo,nam,'UOM'):- !.

neClassType('Person',per,nam,'PER'):- !.
neClassType('Organization',org,nam,'ORG'):- !.
neClassType('Location',geo,nam,'LOC'):- !.
neClassType('Artifact',art,nam,'ART'):- !.
neClassType('Event',eve,nam,'HAP'):- !.
neClassType('Natural_Object',nat,nam,'NAT'):- !.
neClassType('Time',tim,nam,'TIM'):- !.
neClassType('GPE',gpe,nam,'GPE'):- !.

neClassType(N,Class,Type,Tag):- atom(N), atomic_list_concat([Class,Type],'-',N), neClassType(_,Class,_,Tag), !.
neClassType(_,nam,nam,'UNK'):- !.
neClassType(_,_,_,'UNK').

neClassType(N,Class,Type):- atom(N), atomic_list_concat([Class,Type],'-',N), !.
neClassType(_,nam,nam).

neClass(N,C):- neClassType(N,C,_).
