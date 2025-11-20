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

printOnlyInteresting := true;
// a>=2, b>=a+1, c>=2, d>=1, {a,b,c} pairwise coprime, {c,d} coprime
case 100:
	when 0: semigroup := [10,15,36];
	when 1: semigroup := [10,15,36];
	when 2: semigroup := [8,12,26,53];
	when 3: semigroup := [6,7];
	when 4: semigroup := [4,10,23];
	when 5: semigroup := [8,12,29];
	when 6: semigroup := [12,18,39,79];
	when 7: semigroup := [18,45,93,281];
	when 8: semigroup := [36,96,292,881];
	//
	when 100: abcd := [2,3,5,2];
	when 101: abcd := [2,3,5,2];
	when 102: abcd := [3,8,7,1];
	when 103: abcd := [4,7,3,1];
	//
	when 900:
		// 10-15-36
		P<x,y> := LocalPolynomialRing(Q,2); R:=Q;
		f := (y^2-x^3)^5 + x^18;
		maxContact := [P| x, y, y^2-x^3, f ];
		semigroup := SemiGroup(f);
	else:
		error "Invalid choice of curve.";
end case;


//##################
//### Curve data
//##################

if not assigned f then
	if assigned abcd then 
		a,b,c,d := Explode(abcd); semigroup := [a*c,b*c,a*b*(c+d)];
	end if;
	f, maxContact := ExampleCurve(semigroup);
	P := Parent(f); x:=P.1; y:=P.2; R := BaseRing(P);
end if;
PNotLocal<X,Y> := PolynomialRing(Q,2);

g := #semigroup -1;
mu := MilnorNumber(f);
//printf "f = %o\n", f;
//print "maxContact ="; print maxContact;
Prf, ef := ProximityMatrix(semigroup);
numPoints := Ncols(Prf);
vf := ef * Transpose(Prf^-1);
N := -Transpose(Prf) * Prf;
excf := ef * Prf; //vf * (-N);
M := N; for i in [1..numPoints] do M[i][i] := 0; end for;

isFree := [ &+Eltseq(Prf[pt]) ge 0 : pt in [1..numPoints]];
isRupture := [ (&+Eltseq(M[pt]) ge 3) or (pt eq numPoints and &+Eltseq(M[pt]) ge 2) : pt in [1..numPoints]];

diagramData := diagramDataFromProximity(Prf); // For plots

printf "\n";
printf "Semigroup %o\n", semigroup;
printf "mu=%o\n", mu;
printf "\n";

printf "Points:\n";
annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations);
printf "\n";

printf "Multiplicities (e):\n";
annotations := ef[1];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations);
printf "\n";

printf "Values (v):\n";
annotations := vf[1];
printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations);
printf "\n";

printf "Calculating jumping numbers...\n";
printf "Done calculating JN.\n";
JNbyRupture := JumpingNumbers(semigroup);
JNbyRuptureSets := [Seqset(JNbyRupture[i]) : i in [1..g]];
allJN := {*Z| *}; // multiset
for i in [1..g] do
	allJN join:= SetToMultiset(JNbyRuptureSets[i]);
end for;
repeatedJN := [<JN,m> : JN->m in allJN | m gt 1 ];
Sort(~repeatedJN);
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
//##################################################

print "Calculating filtration...";
case 1:
	when 1:
		filtration := Filtration(f : N:=mu);
		filtration := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration];
	when 2:
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

print "Calculating log resolutions and related data...";
//print Universe(filtration[1][1]);
filtrationIdeals := [];
filtrationIdealToSequence := AssociativeArray();
idealToIntersectionMult := AssociativeArray();
idealToDimension := AssociativeArray();
idealToPr := AssociativeArray();
idealTo_v := AssociativeArray();
idealTo_e := AssociativeArray();
idealToExc := AssociativeArray();
for gen_and_int in filtration do
	generators, intersection := Explode(gen_and_int);
	I := ideal<P| generators>;
	Append(~filtrationIdeals, I);
	idealToIntersectionMult[I] := intersection;
	filtrationIdealToSequence[I] := generators;
	
	Pr, v := LogResolution(I);
	e := v * Transpose(Pr);
	exc := e * Pr;
	idealToPr[I] := Pr;
	idealTo_v[I] := v;
	idealTo_e[I] := e;
	idealToExc[I] := exc;
	INotLocal := ideal<PNotLocal| [Evaluate(gen,[X,Y]) : gen in Basis(I)]>;
	idealToDimension[I] := Dimension(PNotLocal/INotLocal);
end for;
filtrationIdealsSet := Seqset(filtrationIdeals);

if multipliers[1][2] eq 0 then Remove(~multipliers, 1); end if; // remove JN=0
multiplierIdeals := [];
multiplierIdealToJN := AssociativeArray();
multiplierIdealToSequence := AssociativeArray();
dimToMultiplier := AssociativeArray();
for gen_and_JN in multipliers do
	generators, JN := Explode(gen_and_JN);
	I := ideal<P| generators>;
	Append(~multiplierIdeals, I);
	multiplierIdealToJN[I] := JN;
	multiplierIdealToSequence[I] := generators;
	if I notin filtrationIdeals then
		Pr, v := LogResolution(I);
		e := v * Transpose(Pr);
		exc := e * Pr;
		idealToPr[I] := Pr;
		idealTo_v[I] := v;
		idealTo_e[I] := e;
		idealToExc[I] := exc;
		INotLocal := ideal<PNotLocal| [Evaluate(gen,[X,Y]) : gen in Basis(I)]>;
		dim := Dimension(PNotLocal/INotLocal);
		idealToDimension[I] := dim;
		intMult := &+[Z| e[1][i] * ef[1][i] : i in [1..Ncols(e)]];
		idealToIntersectionMult[I] := intMult;
		dimToMultiplier[dim] := I;
	end if;
end for;
multiplierIdealsSet := Seqset(multiplierIdeals);

multiplierIdealsNotInFiltration := multiplierIdealsSet diff filtrationIdealsSet;
JNOfMultiplierIdealsNotInFiltration := [multiplierIdealToJN[I] : I in multiplierIdealsNotInFiltration];
Sort(~JNOfMultiplierIdealsNotInFiltration);

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;

procedure printIdealData(I)
	printf "\n";
	IndentPush(2);
	//print LogResolution(I);
	Pr := idealToPr[I];
	v := idealTo_v[I];
	e := idealTo_e[I];
	exc := idealToExc[I];
	annotations := Eltseq(exc) cat [Z|0:i in [Ncols(e)..numPoints]];
	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations);
	//printAnnotatedEnriquesDiagram(diagramData, annotations);
	//printAnnotatedDualGraph(diagramData, annotations);
	//printf "e = %o\n", e;
	//vUnload := Unloading(Transpose(Pr)*Pr,v);
	//eUnload := vUnload * Transpose(Pr);
	//printf "vUnload = %o\n", vUnload;
	//printf "eUnload = %o\n", eUnload;
	IndentPop(2);
end procedure;

print "Done calculating.";
printf "\n";


//##################################################
//### Calculate filtration and multiplier ideals
//##################################################

printf "JN of multiplier ideals not in the filtration (#=%o):\n", #multiplierIdealsNotInFiltration;
for i->JN in JNOfMultiplierIdealsNotInFiltration do
	if i gt 1 then printf ", "; end if;
	printf "%o", JN;
end for;
printf "\n";

printf "\n";

// Compare filtration vs multipliers

print "----------------------------------------------";
print ".    -> Multiplier ideal in the filtration";
print "Y/NO -> Filtration ideal is a multiplier ideal";
print "!!!! -> Multiplier ideal is not in filtration ";
print "Enriques diagram and dual graph -> excesses";
print "----------------------------------------------";
printf "\n";


for idx->I in filtrationIdeals do
	isInteresting := true;
	if printOnlyInteresting then
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
			printf "   Y [K·Ki]=%-4o JN=%-8o dim(C[x,y]/I)=%o ", idealToIntersectionMult[I], multiplierIdealToJN[I], idealToDimension[I];
			SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
			//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			//printf "\n";
			printIdealData(I);
		else
			printf "NO   [K·Ki]=%-4o    %-8o dim(C[x,y]/I)=%o ", idealToIntersectionMult[I], " ", idealToDimension[I];
			SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
			//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			//printf "\n";
			printIdealData(I);
			dim := idealToDimension[I];
			if IsDefined(dimToMultiplier, dim) then
				printf "\n";
				MI := dimToMultiplier[dim];
				printf "!!!! [K·Ki]=%-4o JN=%-8o dim(C[x,y]/I)=%o ", idealToIntersectionMult[MI], multiplierIdealToJN[MI], idealToDimension[MI];
				SNice, extras := MonomialSequence(multiplierIdealToSequence[MI], maxContact);
				printIdealData(MI);
			end if;
		end if;
	else
		printf ".";
	end if;
end for;
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









printf "\n\nFinished\n";
quit;

