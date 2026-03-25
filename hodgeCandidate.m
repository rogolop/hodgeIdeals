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

printDiagrams           := false;
printDiagramsSideBySide := true;
quitOnFinish            := true;

R:=Q; P<x,y>:=LocalPolynomialRing(R,2);
//fString := "(y^2-11*x^3)*(y^3-x^4)";
fString := "x^7 + y^3";
f := eval fString;

PNotLocal<X,Y> := PolynomialRing(R,2);

//##################
//### Curve data
//##################

printf "f = %o\n= %o\n", fString, f;

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;


//semigroup := SemiGroup(f);
//
//g := #semigroup -1;
//mu := MilnorNumber(f);
////printf "f = %o\n", f;
////print "maxContact ="; print maxContact;
//Prf, ef := ProximityMatrix(semigroup);
//numPoints := Nco;ls(Prf);
//PrfT := Transpose(Prf);
//PrfTInv := PrfT^-1;
//vf := ef * PrfTInv;
//N := -PrfT * Prf;
//excf := ef * Prf; //vf * (-N);
//M := N; for i in [1..numPoints] do M[i][i] := 0; end for;
//
//planeBranchNumbers := PlaneBranchNumbers(semigroup);
//g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
//
//isFree := [ &+Eltseq(Prf[pt]) ge 0 : pt in [1..numPoints]];
//isRupture := [ (&+Eltseq(M[pt]) ge 3) or (pt eq numPoints and &+Eltseq(M[pt]) ge 2) : pt in [1..numPoints]];
//
//diagramData := diagramDataFromProximity(Prf); // For plots
//
//printf "\n";
//printf "Semigroup %o\n", semigroup;
//printf "\n";
//printf "f = %o\n",f;
//printf "\n";
//
//if printDiagrams then
//	printf "Points:\n";
//	annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
//	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
//	printf "\n";
//
//	printf "Multiplicities (e):\n";
//	annotations := ef[1];
//	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
//	printf "\n";
//
//	printf "Values (v):\n";
//	annotations := vf[1];
//	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
//	printf "\n";
//end if;

//##################################################
//### Calculate ideals
//##################################################

Nf := NewtonPolygon(f); // Points
sides := NewtonSides(f, Nf); // For each side: <n, m, F_Gamma(Z)> with n=h(Gamma)

// Weights for side with slope -n/m, containing point (a,b) in Nf:
// (1/m, 1/n) * 1/(a/m + b/n) = ( 1/(a+b*m/n), 1/(a*n/m+b) ) = ( n/(na+mb), m/(na+mb) )
weights := []; // Zhang: B_F
for i in [1..#sides] do
	n := sides[i][1];
	m := sides[i][2];
	a := Nf[i][1];
	b := Nf[i][2];
	Append(~weights, <n/(n*a+m*b), m/(n*a+m*b)>);
end for;
printf "weights: %o\n", weights;
offsets := [ws[1] + ws[2] : ws in weights];
printf "offsets: %o\n", offsets;

function rhoTilde(ab) // Zhang: rho tilde
	min := Min([offsets[i] + weights[i][1]*ab[1] + weights[i][2]*ab[2] : i in [1..#sides]]);
	return min;
end function;

function OTildeGe(rho)
	j := 0;
	while rhoTilde([0,j]) lt rho do
		j +:= 1;
	end while;
	gen := [P| y^j];
	i := 1;
	jLast := j;
	while j gt 0 do
		jLast := j;
		while rhoTilde([i,j]) ge rho do
			j -:= 1;
		end while;
		j +:= 1;
		if j lt jLast then
			Append(~gen, x^i * y^j);
		end if;
		i +:= 1;
	end while;
	//return Reduce(Basis(ideal<PNotLocal|gen>));
	return gen;
end function;

function Der(f, i)
	P := Parent(f);
	df := P!0;
	for t in Terms(f) do
		d := Degree(t,i);
		if d gt 0 then
			df +:= d * Evaluate(t, i, 1) * P.i^(d-1);
		end if;
	end for;
	return df;
end function;

function HodgeCandidate(k, alpha)
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
	Ra<a> := RationalFunctionField(R,1);
	Pa := LocalPolynomialRing(Ra,2);
	AssignNames(~Pa, ["x","y"]);
	x := Pa.1;
	y := Pa.2;
	fa := Evaluate(f, [x,y]);
	gen := [Pa| Evaluate(g, [x,y]) : g in OTildeGe(alpha + k)];
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeCandidate(k-1, alpha);
		moreGen := &cat[[fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
			fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2)] :
			g in Hodge_kMinus1 ];
		gen cat:= moreGen;
	end if;
	
	//PaNotLocal := PolynomialRing(R,3);
	//return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	PaNotLocal := PolynomialRing(Ra,2);
	return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	//return gen;
end function;


procedure printHodgeCandidate(k, alpha)
	I := HodgeCandidate(k, alpha);
	printf "I_%o(f^%o) =?= ", k, alpha; prt(I); printf "\n";
end procedure;

//O := OTildeGe(3);
//printf "Õ^{>=1} = "; prt(O); printf "\n";

printHodgeCandidate(0, 1/21);
printHodgeCandidate(0, 10/21);
printHodgeCandidate(0, 11/21);
printHodgeCandidate(0, 13/21);
printHodgeCandidate(0, 16/21);
printHodgeCandidate(0, 17/21);
printHodgeCandidate(0, 19/21);
printHodgeCandidate(0, 20/21);
printHodgeCandidate(0, 1);
print "---";
printHodgeCandidate(1, 1/21);
printHodgeCandidate(1, 2/21);
printHodgeCandidate(1, 4/21);
printHodgeCandidate(1, 5/21);
printHodgeCandidate(1, 8/21);
printHodgeCandidate(1, 10/21);
printHodgeCandidate(1, 11/21);
printHodgeCandidate(1, 13/21);
printHodgeCandidate(1, 16/21);
printHodgeCandidate(1, 17/21);
printHodgeCandidate(1, 19/21);
printHodgeCandidate(1, 20/21);
printHodgeCandidate(1, 1);

printf "\n\nFinished\n";
if quitOnFinish then
	quit;
end if;



