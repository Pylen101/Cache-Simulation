%GENERAL
%convertBinToDec/2
%Needed in Bin to Dec calculation

exp(_,0,1).
exp(X,Y,Z):-
	Y > 0,
	Y1 is Y - 1,
	exp(X,Y1,Z1),
	Z is Z1*X.

convertBinToDec(Bin,Dec):-
	number_string(Bin,S), %convert number to String
	string_chars(S,L), %convert String into list of characters
	length(L,N), %acquire length of string to check index of each number
	N1 is N-1, %subtract length by 1 to get index of the MSB
	convertBinToDec(L,Dec,N1). %recursion on List (LETS GO)
convertBinToDec([H|T],Dec,N):-
	atom_number(H,X), % convert the atom (char) into int
	exp(2,N,B),
	N1 is N -1,
	convertBinToDec(T,Dec1,N1),
	Dec is Dec1 + B*X.

convertBinToDec([],0,_).

%replaceIthItem/4

replaceIthItem(X,[H|T],I,R):-
	replaceIthItem(X,[H|T],0,I,R).
replaceIthItem(X,[_|T],I,I,[X|T]).
replaceIthItem(X,[H1|T1],Count,I,[H2|T2]):-
	H1 \= X,
	H1 = H2,
	Count1 is Count + 1,
	replaceIthItem(X,T1,Count1,I,T2).

%splitEvery/3

splitEvery(_,[],[]).
splitEvery(N, [H|T], [X|T1]):-
	append(X,Y,[H|T]), %append can be used to get more than 1 combination
	length(X,N),
	splitEvery(N,Y,T1).




% logBase2/2

logBase2(0,1).
logBase2(N,P):-
	logBase2(N,P,0).

logBase2(1,Acc,Acc). %Acc is used to make stuff easier
logBase2(N,P,Acc):-
	0 is N mod 2, %check if N is divisable by 2 always
	N1 is N//2,
	Acc1 is Acc +1,
	logBase2(N1,P,Acc1).

% getNumBits/4

getNumBits(_,fullyAssoc,_,0).
getNumBits(NumOfSets,setAssoc,Cache,BitsNum):-
	length(Cache,N),
	N1 is N//NumOfSets, % options in 1 set
	logBase2(N1,BitsNum).
getNumBits(_,directMap,Cache,BitsNum):-
	length(Cache,N),
	logBase2(N,BitsNum).



%fillZeros/4

fillZeros(S,N,R):-
	string_chars(S,L),
	fillZerosList(L,N,L2),
	atomics_to_string(L2,R).

fillZerosList(R,0,R).
fillZerosList([H|T],N,R):-
	N>0,
	N1 is N - 1,
	append(['0'],[H|T],R1),
	fillZerosList(R1,N1,R).

%replacement/8 Direct Mapping

replaceInCache(Tag,Idx,Mem,OldCache,NewCache,ItemData,
directMap,BitsNum):-
	number_string(Tag,S1), % String of Tag
	number_string(Idx,S2), % String of Idx
	string_to_list(S2,C1), % In case Idx had bin < BitsNum
	length(C1,N1),
	A is BitsNum - N1,
	fillZeros(S2,A,S22),
	string_concat(S1,S22,S3), % String of Address
	atom_number(S3,Address), % get Binary of address
	convertBinToDec(Address,AddInBin), % get decimal of address
	nth0(AddInBin,Mem,ItemData), % get ItemData at address
	string_to_list(S1,C2), % getting a list with length = N
	length(C2,N2), % N = number number of bits in current tag
	B is BitsNum + N2,
	Z is 6 - B, % getting number of zeros missing
	fillZeros(S1,Z,R), % Getting the full binary Tag
	convertBinToDec(Idx,ID), % Getting the decimal of index
	changeCache(R,ID,ItemData,OldCache,NewCache).

changeCache(Tag,0,ItemData,[_|T],[item(tag(Tag),data(ItemData),1,0)|T]).
changeCache(Tag,Idx,ItemData,[H1|T1],[H2|T2]):-
	Idx > 0,
	H1 = H2,
	Idx1 is Idx -1,
	changeCache(Tag,Idx1,ItemData,T1,T2).

%replacement/8 Fully-Associative

maximum(X,Y,X) :- X>=Y.
maximum(X,Y,Y) :- Y>X.

replaceInCache(Tag,0,Mem,OldCache,NewCache,ItemData,fullyAssoc,
_):-
	number_string(Tag,S1), % String of Tag
	atom_number(S1,Address), % get Binary of address
	convertBinToDec(Address,AddInBin), % get decimal of address
	nth0(AddInBin,Mem,ItemData), % get ItemData at address
	string_to_list(S1,C2), % getting a list with length = N
	length(C2,N), % N = number number of bits in current tag
	Z is 6 - N, % getting number of zeros missing
	fillZeros(S1,Z,R), % Getting the full binary Tag
	checkIfValid(OldCache,V),  % V acts as a checker as to which is used (Order or ValidBit)
	changeUsingValid(R,OldCache,NewCache,ItemData,V), % if V = 0 change using Valid
        getMaxOrder(OldCache,MaxOrder),
	changeUsingOrder(R,ItemData,MaxOrder,OldCache,NewCache,V). % if V = 1 change using Order


changeUsingValid(_,_,_,_,1).
changeUsingValid(Tag,[item(_,_,0,_)|T],[item(tag(Tag),data(ItemData),1,0)|T2],ItemData,0):-
	incrementOrder(T,T2).
changeUsingValid(Tag,[item(tag(Tag2),Data,ValidBit,Order)|T],[H2|T2],ItemData,0):-
	ValidBit == 1,
	Order2 is Order +1,
	H2 = item(tag(Tag2),Data,ValidBit,Order2),
	changeUsingValid(Tag,T,T2,ItemData,1).

incrementOrder([],[]).
incrementOrder([item(Tag,Data,0,Order)|T1],[item(Tag,Data,0,Order)|T2]):-
	incrementOrder(T1,T2).
incrementOrder([item(Tag,Data,1,Order)|T1],[item(Tag,Data,1,Order2)|T2]):-
	Order2 is Order + 1,
	incrementOrder(T1,T2).

getMaxOrder([],0).
getMaxOrder([item(_,_,_,Order)|T],M):-
	getMaxOrder(T,M1),
	maximum(Order,M1,M).

checkIfValid([],1).
checkIfValid([item(_,_,ValidBit,_)|T],V):-
	checkIfValid(T,V1),
	V is V1*ValidBit.

changeUsingOrder(_,_,_,_,_,0).
changeUsingOrder(Tag,ItemData,MaxOrder,[item(_,_,1,MaxOrder)|T],[item(tag(Tag),data(ItemData),1,0)|T2],1):-
	incrementOrder(T,T2).
changeUsingOrder(Tag, ItemData, MaxOrder, [item(tag(Tag2),Data,1,Order)|T], [H2|T2], 1):-
	Order \= MaxOrder,
	Order2 is Order + 1,
	H2 = item(tag(Tag2),Data,1,Order2),
	changeUsingOrder(Tag,ItemData,MaxOrder,T,T2,1).

replace(0, X, [_|T], [X|T]).
replace(N, X, [H|T],[H|T2]):-
	N > 0,
	N1 is N -1,
	replace(N1,X,T,T2).

%SET-ASSOCIATIVE

getDataFromCache(StringAddress,Cache,Data,HopsNum,setAssoc,SetsNum):-
	length(Cache,CacheLength),
	getNumBits(SetsNum,setAssoc,Cache,BitsNumNeeded),
	LengthPerSet is CacheLength / SetsNum,
	splitEvery(LengthPerSet,Cache,SplitCache),
	number_string(NumberAddress,StringAddress),
	convertAddress(NumberAddress,SetsNum,Tag,Idx,setAssoc),
	convertBinToDec(Idx,IdxDec),
	getHelperSet(Tag,SplitCache,Data,HopsNum,IdxDec,BitsNumNeeded).

getHelperSet(Tag,[H|T],Data,Hopsnum,0,BitsNumNeeded):-
	number_string(Tag,TagStringNoZeroes),
	string_length(TagStringNoZeroes,TagLength),
	N is 6-(TagLength+BitsNumNeeded),
	fillZeros(TagStringNoZeroes,N,StringTag),
	getHelperSet1(StringTag,H,Data,Hopsnum).

getHelperSet(Tag,[H|T],Data,Hopsnum,Index,BitsNumNeeded):-
	Index\=0,
	Index2 is Index-1,
	getHelperSet(Tag,T,Data,Hopsnum,Index2,BitsNumNeeded).

getHelperSet1(Tag,[H|T],Data,0):-
	H=item(tag(Tag),data(Data),1,_).

getHelperSet1(Tag,[H|T],Data,NumsBit):-
	H=item(tag(M),,,_),
	M\=Tag,
	getHelperSet1(Tag,T,Data,Nums2),
	NumsBit is (Nums2 + 1).

removeNumFromList(L,0,L,[]).
removeNumFromList([],N,L,M):-
	N\=0,
	N2 is N-1,
	removeNumFromList([],N2,L,M2),
	append(M2,['0'],M).
removeNumFromList([H|T],Num,L,M):-
	Num2 is (Num-1),
	removeNumFromList(T,Num2,L,M1),
	append(M1,[H],M).

convertAddress(Bin,SetsNum,Tag,Idx,setAssoc):-
	logBase2(SetsNum,I),
	number_string(Bin, BinString),
	string_chars(BinString, BinCharsL),
	reverse(BinCharsL,BinCharsL2),
	removeNumFromList(BinCharsL2,I,TagRevL,IdxL),
	reverse(TagRevL,TagL),
	string_chars(TagS,TagL),
	string_chars(IdxS,IdxL),
	checkIfZero(TagS,Tag),
	checkIfZero(IdxS,Idx).

checkIfZero(String,Number):-
	String = "",
	Number = 0 .

checkIfZero(String,Number):-
	String\="",
	number_string(Number,String).

reverse(Xs, Ys) :-
  reverse(Xs, [], Ys, Ys).
reverse([], Ys, Ys, []).
reverse([X|Xs], Rs, Ys, [_|Bound]) :-
  reverse(Xs, [X|Rs], Ys, Bound).

%replacement/8 Set-Associative


replaceInCache(Tag,Idx,Mem,OldCache,NewCache,ItemData,
setAssoc,SetsNum):-
	number_string(Tag,S1), % String of Tag
	number_string(Idx,S2), % String of Idx
	string_to_list(S2,C1), % In case Idx had bin < BitsNum
	length(C1,N1),
	logBase2(SetsNum,BitsNum),
	A is BitsNum - N1,
	fillZeros(S2,A,S22),
	string_concat(S1,S22,S3), % String of Address
	atom_number(S3,Address), % get Binary of address
	convertBinToDec(Address,AddInBin), % get decimal of address
	nth0(AddInBin,Mem,ItemData), % get ItemData at address
	string_to_list(S1,C2), % getting a list with length = N
	length(C2,N2), % N = number number of bits in current tag
	B is BitsNum + N2,
	Z is 6 - B, % getting number of zeros missing
	fillZeros(S1,Z,R), % Getting the full binary Tag String
	length(OldCache,N),
	Part is N // SetsNum,
	splitEvery(Part,OldCache,L),
	convertBinToDec(Idx,IdxDec),
	nth0(IdxDec,L,OldSet),
	checkIfValid(OldSet,V),
	changeUsingValid(R,OldSet,NewSet,ItemData,V),
	getMaxOrder(OldSet,MaxOrder),
	changeUsingOrder(R,ItemData,MaxOrder,OldSet,NewSet,V),
	replace(IdxDec,NewSet,L,L2),
	splitEvery(Part,NewCache,L2).


