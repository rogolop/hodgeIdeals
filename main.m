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

hideCoinciding := false;
printCoincidingIdeals := true;
printExtraFiltrationIdeals := true;
printMissingMultiplierIdeals := true;
case 2:
	when 1:
		semigroup := [10,15,36]; //[8,12,26,53]; //[6,7]; //[10,15,36];
	when 2:
		// a>=2, b>=a+1, c>=2, d>=1, {a,b,c} pairwise coprime, {c,d} coprime
		abcd := [2,3,5,2]; // [2,3,5,2] [3,8,7,1] [4,7,3,1]
end case;

//P<x,y> := LocalPolynomialRing(Q,2); R:=Q;
//f := (y^2-x^3)^5 + x^18; // 10-15-36
//maxContact := [P| x, y, y^2-x^3, f ];
//semigroup := SemiGroup(f);

//######################
//### Everything else
//######################

if not assigned f then
	if assigned abcd then 
		a,b,c,d := Explode(abcd); semigroup := [a*c,b*c,a*b*(c+d)];
	end if;
	f, maxContact := ExampleCurve(semigroup);
	P := Parent(f); x:=P.1; y:=P.2; R := BaseRing(P);
end if;
P2<X,Y> := PolynomialRing(Q,2);

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;


printf "\nSemigroup %o\n", semigroup;
g := #semigroup -1;
mu := MilnorNumber(f);
printf "mu=%o\n", mu;
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

// For plots
dualGraphMatrix := dualGraphPlottingMatrix(Prf);
enriques := enriquesPlottingMatrix(Prf);

// For proximity plot
plotPrf := ZeroMatrix(Z, numPoints);
for i in [1..numPoints], j in [1..i-1] do
	// 1 up, 2 down, 4 right, 8 left
	if Prf[i][j] eq -1 then
		plotPrf[i][j] +:= 1+4;
		if 0 ne &+[Z|Prf[k][j]:k in [i+1..numPoints]] then plotPrf[i][j]+:=2; end if;
		if 0 ne &+[Z|Prf[i][k]:k in [1..j-1]]         then plotPrf[i][j]+:=8; end if;
	else
		if 0 ne &+[Z|Prf[k][j]:k in [i+1..numPoints]] then plotPrf[i][j]+:=1+2; end if;
		if 0 ne &+[Z|Prf[i][k]:k in [1..j-1]]         then plotPrf[i][j]+:=4+8; end if;
	end if;	
end for;

//dualGraphEdges := [];
//for i in [1..numPoints], j in [1..i] do
//	if M[i][j] eq 1 then Append(~dualGraphEdges, <j,i>); end if;
//end for;



//print "Proximity matrix of f:"; print Prf;
//printf "ef   = %o\n", ef;
//printf "vf   = %o\n", vf;
//printf "excf = %o\n", excf;
//print "Intersection matrix of f:"; print N; printf "\n";
//print M;
//printf "\n"; print dualGraphMatrix;

printf "\n";
printf "Proximity with (e,v):\n";
boxDrawingCharacters := [" ", "╵", "╷", "│", "╶", "└", "┌", "├", "╴", "┘", "┐", "┤", "─", "┴", "┬", "┼"];
for i in [1..numPoints], j in [1..i] do
	if i eq j then printf "%o%o (%o,%o)\n", isRupture[i] select "r" else "p", i-1, ef[1][i], vf[1][i]; continue; end if;
	// 1 up, 2 down, 4 right, 8 left
	printf "%o", boxDrawingCharacters[plotPrf[i][j] +1];
end for;
printf "\n";

printf "Points:\n";
annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
printAnnotatedEnriquesDiagram(enriques, annotations);
printAnnotatedDualGraph(dualGraphMatrix, annotations);
printf "\n";

printf "Multiplicities (e):\n";
annotations := ef[1];
printAnnotatedEnriquesDiagram(enriques, annotations);
printAnnotatedDualGraph(dualGraphMatrix, annotations);
printf "\n";

printf "Values (v):\n";
annotations := vf[1];
printAnnotatedEnriquesDiagram(enriques, annotations);
printAnnotatedDualGraph(dualGraphMatrix, annotations);
printf "\n";

//printf "\nDual graph with (e,v) and *=rupture:\n";
////printAnnotatedDualGraph(dualGraphMatrix, [Sprintf("p%o%o(%o,%o)", pt-1, isRupture[pt]select"*"else"_", ef[1][pt], vf[1][pt]) : pt in [1..numPoints]] : vertSep:="|\n");

//printf "\n"; printAnnotatedDualGraph(dualGraphMatrix, [Sprintf("p%o(%o,%o)", pt-1, ef[1][pt], vf[1][pt]) : pt in [1..numPoints]] : horizSep:="___");

//printf "\n"; printAnnotatedDualGraph(dualGraphMatrix, [Sprintf("%o%o~%o", isRupture[pt]select"*"else"_", ef[1][pt], vf[1][pt]) : pt in [1..numPoints]] : horizSep:="___");

//printf "\n"; printAnnotatedDualGraph(dualGraphMatrix, [isRupture[pt]select"*"else"o": pt in [1..numPoints]]);





// Calculate

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
multipliers := MultiplierIdeals(f);

// Prepare

//print Universe(filtration[1][1]);
filtrationIdeals := [];
filtrationIdealToInt := AssociativeArray();
filtrationIdealToSequence := AssociativeArray();
for gen_and_int in filtration do
	generators, intersection := Explode(gen_and_int);
	I := ideal<P| generators>;
	Append(~filtrationIdeals, I);
	filtrationIdealToInt[I] := intersection;
	filtrationIdealToSequence[I] := generators;
end for;

if multipliers[1][2] eq 0 then Remove(~multipliers, 1); end if; // remove JN=0
multiplierIdeals := [];
multiplierIdealToJN := AssociativeArray();
multiplierIdealToSequence := AssociativeArray();
for gen_and_JN in multipliers do
	generators, JN := Explode(gen_and_JN);
	I := ideal<P| generators>;
	Append(~multiplierIdeals, I);
	multiplierIdealToJN[I] := JN;
	multiplierIdealToSequence[I] := generators;
end for;

// Compare filtration vs multipliers

print "Data:";
print "- Filtration ideal is a multiplier ideal (Y/NO)";
print "- Intersection multiplicity of the clusters?";
print "- Jumping number, or ideal that is not a multiplier ideal";
print "- dimension of C[x,y] / I";
print "- Excesses";
printf "\n";

procedure printIdealData(I)
	IndentPush(5);
	I2 := ideal<P2| [Evaluate(gen,[X,Y]) : gen in Basis(I)]>;
	printf "dim R/I = %o\n", Dimension(P2/I2);
	//print LogResolution(I);
	Pr, v := LogResolution(I);
	e := v * Transpose(Pr);
	exc := e * Pr;
	annotations := Eltseq(exc) cat [Z|0:i in [Ncols(e)..numPoints]];
	printAnnotatedEnriquesDiagram(enriques, annotations);
	printAnnotatedDualGraph(dualGraphMatrix, annotations);
	//printf "e = %o\n", e;
	vUnload := Unloading(Transpose(Pr)*Pr,v);
	eUnload := vUnload * Transpose(Pr);
	//printf "vUnload = %o\n", vUnload;
	//printf "eUnload = %o\n", eUnload;
	IndentPop(5);
end procedure;

I124 := [];
I127 := [];
MI161_210 := [];

multiplierIdealsCopy := multiplierIdeals;
for I in filtrationIdeals do
	//if filtrationIdealToInt[I] eq 124 then I124 := I; end if;
	//if filtrationIdealToInt[I] eq 127 then I127 := I; end if;
	
	if I in multiplierIdealsCopy then
		Exclude(~multiplierIdealsCopy, I);
		if not hideCoinciding then
			printf "   Y %-4o %-8o ", filtrationIdealToInt[I], multiplierIdealToJN[I];
			if printCoincidingIdeals then
				SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
				//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
				//printf "\n";
				printIdealData(I);
			end if;
			printf "\n";
		end if;
	else
		printf "NO   %-4o ", filtrationIdealToInt[I];
		// printf "        ";
		if printExtraFiltrationIdeals then
			SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
			//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			//printf "\n";
			printIdealData(I);
		end if;
		printf "\n";
	end if;
end for;
printf "\n\nMultiplier ideals that are not in the filtration:\n\n";
if #multiplierIdealsCopy eq 0 then
	printf "None\n";
else
	for I in multiplierIdealsCopy do
		//if multiplierIdealToJN[I] eq 161/210 then MI161_210 := I; end if;
		printf "JN=%-8o ", multiplierIdealToJN[I];
		if printMissingMultiplierIdeals then
			SNice, extras := MonomialSequence(multiplierIdealToSequence[I], maxContact);
			//prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			//printf "\n";
			printIdealData(I);
		end if;
		printf "\n";
	end for;
end if;

printf "\nTotal number of missing multiplier ideals: %o\n\n", #multiplierIdealsCopy;

//print "I124";
////print I124;
//I124 := ideal<P2| [Evaluate(gen,[X,Y]) : gen in Basis(I124)]>;
////print I124;
//printf "dim = %o\n", Dimension(P2/I124);
//printf "\n";
//print "MI161_210";
////print MI161_210;
//MI161_210 := ideal<P2| [Evaluate(gen,[X,Y]) : gen in Basis(MI161_210)]>;
////print MI161_210;
//printf "\n";
//printf "dim = %o\n", Dimension(P2/MI161_210);
//printf "\n";
//print "I127";
////print I127;
//I127 := ideal<P2| [Evaluate(gen,[X,Y]) : gen in Basis(I127)]>;
////print I127;
//printf "dim = %o\n", Dimension(P2/I127);
//print "----------------------";
//printf "\n";
//
//print "MI : I124";
//print ColonIdeal(MI161_210, I124);
//printf "\n";
//print "I124 : MI";
//print ColonIdeal(I124, MI161_210);
//printf "\n";
//print "MI : I127";
//print ColonIdeal(MI161_210, I127);
//printf "\n";
//print "I127 : MI";
//print ColonIdeal(I127, MI161_210);
//printf "\n";
//print "I124 : I127";
//print ColonIdeal(I124, I127);
//printf "\n";
//print "I127 : I124";
//print ColonIdeal(I127, I124);


// Print all





printf "\n\nFinished\n";
quit;

