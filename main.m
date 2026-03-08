AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Attach("MonomialSequence.m");
Attach("ExampleCurve.m");
Attach("planeCurveDiagrams.m");
import "SingularitiesDim2/IntegralClosure.m": Unloading;
Z := IntegerRing();
Q := RationalField();

//######################
//### Input/settings
//######################

printOnlyInterestingIdeals := false;
printDiagramsSideBySide    := true;
printGenerators            := true;
printExcesses              := true;
printMultiplicities        := true;
printValues                := true;
quitOnFinish               := true;

case 903:
	when 0: semigroup := [10,15,36];
	when 1: semigroup := [10,15,36];
	when 2: semigroup := [8,12,26,53];
	when 3: semigroup := [6,7];
	when 4: semigroup := [4,10,23];
	when 5: semigroup := [8,12,29];
	when 6: semigroup := [12,18,39,79];
	when 7: semigroup := [18,45,93,281];
	when 8: semigroup := [36,96,292,881];
	when 9: semigroup := [24,55];
	when 10: semigroup := [6,14,43];
	when 11: semigroup := [10,15,42];
	when 12: semigroup := [6,14,45];
	when 13: semigroup := [6,14,53];
	when 14: semigroup := [2*8,2*19,305];
	//
	// a>=2, b>=a+1, c>=2, d>=1, {a,b,c} pairwise coprime, {c,d} coprime
	when 100: abcd := [2,3,5,2];
	when 101: abcd := [2,3,5,2];
	when 102: abcd := [3,8,7,1];
	when 103: abcd := [4,7,3,1];
	when 104: abcd := [3,4,5,1];
	when 105: abcd := [3,5,2,1];
	//
	// n1,n2,n3>=2, n1>a, n2>b, n3>c
	//  pairwise coprime: {n1,n2,n3,a}, {n2,n3,b}, {n3,c}
	when 200: n1n2n3abc := [2,3,5,7,4,6]; printDiagramsSideBySide := false;
	when 201: n1n2n3abc := [2,3,5,7,4,6]; printDiagramsSideBySide := false;
	when 202: n1n2n3abc := [5,3,2,7,5,3]; printDiagramsSideBySide := false;
	when 203: n1n2n3abc := [ 3, 2, 5, 7, 3, 7 ]; printDiagramsSideBySide := false;
	when 204: n1n2n3abc := [ 3, 2, 7, 5, 3, 8 ]; printDiagramsSideBySide := false;
	when 205: n1n2n3abc := [ 3, 2, 5, 7, 3, 6 ]; printDiagramsSideBySide := false;
	//
	when 900:
		R:=Q; P<x,y>:=LocalPolynomialRing(R,2);
		f := (y^2-x^3)^5 + x^18; // 10-15-36
		maxContact := [P|x,y, y^2-x^3, f ];
	when 901:
		R<l>:=RationalFunctionField(Q,1); P<x,y>:=LocalPolynomialRing(R,2);
		f := y^3 - x^7 + l*x^5*y^1;
		maxContact := [P|x,y, f ];
	when 902:
		R<l>:=RationalFunctionField(Q,1); P<x,y>:=LocalPolynomialRing(R,2);
		f := (y+l*x)^6 - x^7;
		maxContact := [P|x,y, f ];
		
	when 903:
		R:=Q; P<x,y>:=LocalPolynomialRing(R,2);
		f := y^4+x^5;
		maxContact := [P|x,y, f ];
	else:
		error "Invalid choice of curve.";
end case;


//##################
//### Curve data
//##################

if assigned f then
	semigroup := SemiGroup(f);
	error if (not assigned maxContact), "maxContact not assigned.";
else
	if assigned abcd then 
		a,b,c,d := Explode(abcd);
		semigroup := [a*c,b*c,a*b*(c+d)];
	elif assigned n1n2n3abc then
		n1, n2, n3, a, b, c := Explode(n1n2n3abc);
		semigroup := [n1*n2*n3, n2*n3*a, n1*n3*a*b, n1*n2*a*b*c];
	end if;
	f, maxContact := ExampleCurve(semigroup);
	P := Parent(f); x:=P.1; y:=P.2; R := BaseRing(P);
end if;
PNotLocal<X,Y> := PolynomialRing(R,2);

g := #semigroup -1;
mu := MilnorNumber(f);
//printf "f = %o\n", f;
//print "maxContact ="; print maxContact;
Prf, ef := ProximityMatrix(semigroup);
numPoints := Ncols(Prf);
PrfT := Transpose(Prf);
PrfTInv := PrfT^-1;
vf := ef * PrfTInv;
N := -PrfT * Prf;
excf := ef * Prf; //vf * (-N);
M := N; for i in [1..numPoints] do M[i][i] := 0; end for;

planeBranchNumbers := PlaneBranchNumbers(semigroup);
g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);

isFree := [ &+Eltseq(Prf[pt]) ge 0 : pt in [1..numPoints]];
isRupture := [ (&+Eltseq(M[pt]) ge 3) or (pt eq numPoints and &+Eltseq(M[pt]) ge 2) : pt in [1..numPoints]];

diagramData := diagramDataFromProximity(Prf); // For plots

printf "\n";
printf "Semigroup %o\n", semigroup;
printf "mu = %o\n", mu;
printf "n = %o\n", ns;
printf "m = %o\n", ms;
printf "_m = %o\n", _ms;
printf "k = %o\n", kps;
printf "N = %o\n", Nps;
for r in [1..g] do
	printf "Gamma_%o = %o\n", r, [ &*(ns[[(j+2)..(r+1)]]) * _ms[j+1] : j in [0..r] ];
end for;
printf "\n";
printf "f = %o\n",f;
printf "\n";

printf "Points:\n";
annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
printf "\n";

printf "Multiplicities (e):\n";
annotations := ef[1];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
printf "\n";

printf "Values (v):\n";
annotations := vf[1];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
printf "\n";

printf "Calculating jumping numbers...\n";
printf "Done calculating JN.\n";
JNbyRupture := JumpingNumbers(semigroup);
//for r in [1..g] do
//	printf "(k_%o + 1) = %-4o, ", r, kps[r]+1;
//	printf "(n_%o + _m_%o)/N_%o = %4o/%-4o = %-9o, ",r,r,r,ns[r+1] + _ms[r+1], Nps[r], (ns[r+1] + _ms[r+1])/Nps[r];
//	printf "(n_%o + _m_%o) - (k_%o + 1) = %o\n",r,r,r,ns[r+1] + _ms[r+1] - (kps[r]+1);
//end for;

printf "JN:\n"; print JNbyRupture;
printf "#JN per rupture divisor: %o\n", [#JN_i : JN_i in JNbyRupture];

JNbyRuptureSets := [Seqset(JNbyRupture[i]) : i in [1..g]];
allJN := {*Z| *}; // multiset
for i in [1..g] do
	allJN join:= SetToMultiset(JNbyRuptureSets[i]);
end for;
repeatedJN := [<JN,m> : JN->m in allJN | m gt 1 ];
Sort(~repeatedJN);
printf "\n";
printf "Repeated JN (#=%o):\n", #repeatedJN;
for i->tup in repeatedJN do
	if i gt 1 then printf ", "; end if;
	printf "%o (%o)", tup[1], tup[2];
end for;
printf "\n";

printf "\n";



//print "Proximity matrix of f:"; print Prf;
//printf "ef   = %o\n", ef;
//printf "vf   = %o\n", vf;
//printf "excf = %o\n", excf;
//print "Intersection matrix of f:"; print N; printf "\n";
//print M;
//printf "\n"; print dualGraphMatrix;
//dualGraphEdges := [];
//for i in [1..numPoints], j in [1..i] do
//	if M[i][j] eq 1 then Append(~dualGraphEdges, <j,i>); end if;
//end for;
//// 1 up, 2 down, 4 right, 8 left
//boxDrawingCharacters := [" ", "╵", "╷", "│", "╶", "└", "┌", "├", "╴", "┘", "┐", "┤", "─", "┴", "┬", "┼"];



//##################################################
//### Calculate filtration and multiplier ideals
//################################################sing##

print "Calculating filtration...";
case 1:
	when 1:
		// Filtration by the curve
		filtration := Filtration(f : N:=mu);
		filtration := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration];
	when 2:
		// Filtration by each rupture divisor, combined, which may not make much sense
		filtration := [];
		for i in [1..g] do
			filtration_i := FiltrationRupture(f,i : N:=mu);
			filtration_i := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration_i];
			for elt in filtration_i do
				if elt notin filtration then Append(~filtration, elt); end if;
			end for;
		end for;
end case;

print "Calculating multiplier ideals...";
multipliers := MultiplierIdeals(f);

print "Preparing data...";
//print Universe(filtration[1][1]);
filtrationIdeals := [];
idealToSequence := AssociativeArray();
idealToIntersectionMult := AssociativeArray();
idealToDimension := AssociativeArray();
idealToIsMultiplier := AssociativeArray();
for gen_and_int in filtration do
	generators, intersection := Explode(gen_and_int);
	I := ideal<P| generators>;
	Append(~filtrationIdeals, I);
	idealToIntersectionMult[I] := intersection;
	idealToSequence[I] := generators;
	
	INotLocal := ideal<PNotLocal| [Evaluate(gen,[X,Y]) : gen in Basis(I)]>;
	idealToDimension[I] := Dimension(PNotLocal/INotLocal);
	
	idealToIsMultiplier[I] := false;
end for;
filtrationIdealsSet := Seqset(filtrationIdeals);

if multipliers[1][2] eq 0 then Remove(~multipliers, 1); end if; // remove JN=0
multiplierIdeals := [];
multiplierIdealToJN := AssociativeArray();
dimToMultiplier := AssociativeArray();
multiplierIdealToMinimalJumpingDivisors := AssociativeArray();
for gen_and_JN in multipliers do
	generators, JN, minimalJumpingDivisors := Explode(gen_and_JN);
	I := ideal<P| generators>;
	Append(~multiplierIdeals, I);
	multiplierIdealToJN[I] := JN;
	multiplierIdealToMinimalJumpingDivisors[I] := [Sprintf("p%o",i-1) : i in minimalJumpingDivisors];
	idealToSequence[I] := generators; // if it is also a filtration ideal, overwrite
	if I notin filtrationIdeals then
		INotLocal := ideal<PNotLocal| [Evaluate(gen,[X,Y]) : gen in Basis(I)]>;
		dim := Dimension(PNotLocal/INotLocal);
		idealToDimension[I] := dim;
		dimToMultiplier[dim] := I;
	end if;
	idealToIsMultiplier[I] := true;
end for;
multiplierIdealsSet := Seqset(multiplierIdeals);

multiplierIdealsNotInFiltration := multiplierIdealsSet diff filtrationIdealsSet;
JNOfMultiplierIdealsNotInFiltration := [multiplierIdealToJN[I] : I in multiplierIdealsNotInFiltration];
Sort(~JNOfMultiplierIdealsNotInFiltration);

printf "Done preparing.\n";

//###################################################
//### Calculate log resolutions and print results
//###################################################

printf "\n";

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;

idealTo_e := AssociativeArray();
idealTo_v := AssociativeArray();
idealTo_exc := AssociativeArray();

procedure CalculateAllMultiplicitiesOfIdeal(~idealToIntersectionMult, ~idealTo_e, ~idealTo_v, ~idealTo_exc, I)
	Pr, v := LogResolution(I);
	e := Transpose(Pr * Transpose(v));
	if Ncols(e) lt numPoints then
		// fill with zeros
		e := Matrix(numPoints, Eltseq(e) cat [Z|0:i in [Ncols(e)+1..numPoints]]);
	end if;
	idealTo_e[I] := e;
	idealTo_v[I] := e * PrfTInv;
	idealTo_exc[I] := e * Prf;
	if idealToIsMultiplier[I] then
		idealToIntersectionMult[I] := &+[Z| e[1][i] * ef[1][i] : i in [1..Ncols(e)]];
	end if;
end procedure;

procedure PrintIdealData(idealToIntersectionMult, idealTo_e, idealTo_v, idealTo_exc, I)
	e := idealTo_e[I];
	v := idealTo_v[I];
	exc := idealTo_exc[I];
	intMult := idealToIntersectionMult[I];

	if idealToIsMultiplier[I] then
		printf "[K·Ki]=%-4o JN=%-8o dim(C[x,y]/I)=%o ", intMult, multiplierIdealToJN[I], idealToDimension[I];
	else
		printf "[K·Ki]=%-4o    %-8o dim(C[x,y]/I)=%o ", intMult, " ", idealToDimension[I];
	end if;
	
	if printGenerators then
		SNice, extras := MonomialSequence(idealToSequence[I], maxContact);
		prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
	end if;
	printf "\n";
	IndentPush(2);
	
	//print LogResolution(I);
	if printExcesses then
		annotations := Eltseq(exc) cat [Z|0:i in [Ncols(e)..numPoints]];
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	end if;
	if printMultiplicities then
		if printExcesses then printf "\n"; end if;
		annotations := Eltseq(e) cat [Z|0:i in [Ncols(e)..numPoints]];
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	end if;
	if printValues then
		if printMultiplicities or printExcesses then printf "\n"; end if;
		annotations := Eltseq(v) cat [Z|0:i in [Ncols(e)..numPoints]];
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	end if;
	//printAnnotatedEnriquesDiagram(diagramData, annotations);
	//printAnnotatedDualGraph(diagramData, annotations);
	//printf "e = %o\n", e;
	//vUnload := Unloading(Transpose(Pr)*Pr,v);
	//eUnload := vUnload * Transpose(Pr);
	//printf "vUnload = %o\n", vUnload;
	//printf "eUnload = %o\n", eUnload;
	IndentPop(2);
end procedure;


printf "JN of multiplier ideals not in the filtration (#=%o):\n", #multiplierIdealsNotInFiltration;
for i->JN in JNOfMultiplierIdealsNotInFiltration do
	if i gt 1 then printf ", "; end if;
	printf "%o", JN;
end for;
printf "\n";

printf "\n";

// Compare filtration vs multipliers

print "----------------------------------------------";
print ".    -> Multiplier ideal in the filtration (not printed)";
print "filt -> Filtration ideal";
print "mult -> Multiplier ideal";
print "Enriques diagram and dual graph: excesses, multiplicities and values";
print "----------------------------------------------";
printf "\n";


for idx->I in filtrationIdeals do
	CalculateAllMultiplicitiesOfIdeal(~idealToIntersectionMult, ~idealTo_e, ~idealTo_v, ~idealTo_exc, I);
	
	isInteresting := true;
	if printOnlyInterestingIdeals then
		if I notin multiplierIdealsSet or
			(idx gt 1 and filtrationIdeals[idx-1] notin multiplierIdealsSet) or
			(idx lt #filtrationIdeals and filtrationIdeals[idx+1] notin multiplierIdealsSet) then
			isInteresting := true;
		else
			isInteresting := false;
		end if;
	end if;
	if isInteresting then
		printf "\n";
		if I in multiplierIdealsSet then
			printf "filt+mult ";
			PrintIdealData(idealToIntersectionMult, idealTo_e, idealTo_v, idealTo_exc, I);
		else
			printf "filt      ";
			PrintIdealData(idealToIntersectionMult, idealTo_e, idealTo_v, idealTo_exc, I);
			dim := idealToDimension[I];
			if IsDefined(dimToMultiplier, dim) then
				printf "\n";
				MI := dimToMultiplier[dim];
				printf "     mult ";
				CalculateAllMultiplicitiesOfIdeal(~idealToIntersectionMult, ~idealTo_e, ~idealTo_v, ~idealTo_exc, MI);
				PrintIdealData(idealToIntersectionMult, idealTo_e, idealTo_v, idealTo_exc, MI);
			end if;
		end if;
	else
		printf ".";
	end if;
end for;
printf "\n";
//printf "\n\nMultiplier ideals that are not in the filtration:\n\n";
//if #multiplierIdealsCopy eq 0 then
//	printf "None\n";
//else
//	for I in multiplierIdealsCopy do
//		printf "     [K·Ki]=%-4o JN=%-8o dim(C[x,y]/I)=%o ", idealToIntersectionMult[I], multiplierIdealToJN[I], idealToDimension[I];
//		//printf "JN=%-8o ", multiplierIdealToJN[I];
//		SNice, extras := MonomialSequence(multiplierIdealToSequence[I], maxContact);
//		//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
//		//printf "\n";
//		printIdealData(I);
//		printf "\n";
//	end for;
//end if;

printf "\n";
printf "________________________________________\n";
printf "\n";
printf "codimension                                                 \n";
printf "|     intersection multiplicity [K·Ki]                      \n";
printf "|     |      Filtration/multiplier(with Multiplicity)       \n";
printf "|     |      |    rupture divisors                          \n";
printf "|     |      |    |     minimal jumping divisors            \n";
printf "|     |      |    |     |       (dis)connected excesses     \n";
printf "|     |      |    |     |       |       jumping number      \n";
printf "|     |      |    |     |       |       |                   \n";
printf "v     v      v    v     v       '-->    '-->                \n";
printf "\n";
dualGraphMatrix := diagramData[1];
dualGraphMainPath := Eltseq(dualGraphMatrix[1]);
firstRupture := Min([p : p in dualGraphMainPath | isRupture[p]]);
firstRupturePosInMainPath := Index(dualGraphMainPath, firstRupture);
for idx->I in filtrationIdeals do
	dim := idealToDimension[I];
	intMult := idealToIntersectionMult[I];
	if I in multiplierIdealsSet then
		printf "d%-4o ", dim;
		printf "i%-4o ", intMult;
		JN := multiplierIdealToJN[I];
		printf (Multiplicity(allJN,JN) gt 1) select " FM   " else " Fm   ";
		for i in [1..g] do
			if JN in JNbyRuptureSets[i] then printf "E%-1o ", i;
			else printf " %-1o ", " "; end if;
		end for;
		
		printf "%o ", multiplierIdealToMinimalJumpingDivisors[I];

		exc := idealTo_exc[I];
		if &+[exc[1][p] : p in dualGraphMainPath[firstRupturePosInMainPath..#dualGraphMainPath]] eq 0 then
			printf "conn ";
		else
			printf "dis  ";
		end if;
		printf "(";
		for p in dualGraphMainPath do
			if isRupture[p] then printf "r"; end if;
			printf "%o ", exc[1][p] eq 0 select "." else exc[1][p];
		end for;
		printf ") ";
		printf "%-9o ", JN;
		//printf "%o", [exc[1][p] : p in dualGraphMainPath];
		printf "\n";
	else
		printf "d%-4o ", dim;
		printf "i%-4o ", intMult;
		printf "F  |  ";
		for i in [1..g] do
			printf " %-1o ", " ";
		end for;
		
		printf "%o ", "       ";
		
		exc := idealTo_exc[I];
		if &+[exc[1][p] : p in dualGraphMainPath[firstRupturePosInMainPath..#dualGraphMainPath]] eq 0 then
			printf "conn ";
		else
			printf "dis  ";
		end if;
		printf "(";
		for p in dualGraphMainPath do
			if isRupture[p] then printf "r"; end if;
			printf "%o ", exc[1][p] eq 0 select "." else exc[1][p];
		end for;
		printf ") ";
		printf "%-9o ", " ";
		printf "\n";
		if IsDefined(dimToMultiplier, dim) then
			MI := dimToMultiplier[dim];
			intMult := idealToIntersectionMult[MI];
			printf "d%-4o ", dim;
			printf "i%-4o ", intMult;
			JN := multiplierIdealToJN[MI];
			printf (Multiplicity(allJN,JN) gt 1) select "|  M  " else "|  m  ";
			for i in [1..g] do
				if JN in JNbyRuptureSets[i] then printf "E%-1o ", i;
				else printf " %-1o ", " "; end if;
			end for;
			
			printf "%o ", multiplierIdealToMinimalJumpingDivisors[MI];
			
			exc := idealTo_exc[MI];
			if &+[exc[1][p] : p in dualGraphMainPath[firstRupturePosInMainPath..#dualGraphMainPath]] eq 0 then
				printf "conn ";
			else
				printf "dis  ";
			end if;
			printf "(";
			for p in dualGraphMainPath do
				if isRupture[p] then printf "r"; end if;
				printf "%o ", exc[1][p] eq 0 select "." else exc[1][p];
			end for;
			printf ") ";
			printf "%-9o ", JN;
			printf "\n";
		end if;
	end if;
end for;









printf "\n\nFinished\n";
if (quitOnFinish) then
	quit;
end if;



