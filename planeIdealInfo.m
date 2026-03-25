AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
//AttachSpec("ZetaFunction/ZetaFunction.spec");
//Attach("MonomialSequence.m");
//Attach("ExampleCurve.m");
Attach("planeCurveDiagrams.m");
//import "SingularitiesDim2/IntegralClosure.m": Unloading;
Z := IntegerRing();
Q := RationalField();

//######################
//### Input/settings
//######################

printEnriques           := true;
printDualGraph          := false;
printDiagramsSideBySide := true;
print_points            := false;
print_v                 := true;
print_e                 := true;
print_exc               := true;
quitOnFinish            := true;

R:=Q; P<x,y>:=LocalPolynomialRing(R,2);

I := [P| x^3, x*y^5];
I := ideal<P| I>;

//######################
//### Do things
//######################

Pr, v, FixedPart, Coeff := LogResolution(I : Coefficients:=true);
PrT := Transpose(Pr);
PrTInv := PrT^-1;
numPoints := Ncols(Pr);
e := Transpose(Pr * Transpose(v));
exc := e * Pr;
diagramData := diagramDataFromProximity(Pr); // For plots

// Unused
N := -PrT * Pr;
M := N; for i in [1..numPoints] do M[i][i] := 0; end for;
isFree := [ &+Eltseq(Pr[pt]) ge 0 : pt in [1..numPoints]];
isRupture := [ (&+Eltseq(M[pt]) ge 3) or (pt eq numPoints and &+Eltseq(M[pt]) ge 2) : pt in [1..numPoints]];



//idealToIntersectionMult[I] := &+[Z| e[1][i] * ef[1][i] : i in [1..Ncols(e)]];

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;

//printf "\n";
printf "I = ";
prt(Basis(I));
printf "\n";
printf "Fixed part: %o\n", FixedPart;

//printf "\n";
//printf "Proximity matrix: \n%o\n", Pr;
//printf "\n";
//printf "v = %o\n", v;
//printf "e = %o\n", e;
//printf "exc = %o\n", exc;
//printf "\n";
//printf "Coefficients:\n"; print Coeff; // ???

if print_points then
	//printf "\n"; printf "Points:\n";
	printf "pts:\n";
	annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
	if printEnriques and printDualGraph then
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	elif printEnriques then
		printAnnotatedEnriquesDiagram(diagramData, annotations);
	elif printDualGraph then
		printAnnotatedDualGraph(diagramData, annotations);
	end if;
end if;
if print_v then
	//printf "\n"; printf "Values (v):\n";
	printf "v:\n";
	annotations := v[1];
	if printEnriques and printDualGraph then
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	elif printEnriques then
		printAnnotatedEnriquesDiagram(diagramData, annotations);
	elif printDualGraph then
		printAnnotatedDualGraph(diagramData, annotations);
	end if;
end if;
if print_e then
	//printf "\n"; printf "Multiplicities (e):\n";
	printf "e:\n";
	annotations := e[1];
	if printEnriques and printDualGraph then
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	elif printEnriques then
		printAnnotatedEnriquesDiagram(diagramData, annotations);
	elif printDualGraph then
		printAnnotatedDualGraph(diagramData, annotations);
	end if;
end if;
if print_exc then
	//printf "\n"; printf "Excesses (exc):\n";
	printf "exc:\n";
	annotations := exc[1];
	if printEnriques and printDualGraph then
		printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	elif printEnriques then
		printAnnotatedEnriquesDiagram(diagramData, annotations);
	elif printDualGraph then
		printAnnotatedDualGraph(diagramData, annotations);
	end if;
end if;
//printf "\n";







//printf "\n\nFinished\n";
if (quitOnFinish) then
	quit;
end if;

