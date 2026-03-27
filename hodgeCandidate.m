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
fString := "y^3 + x^7";
//fString := "x^3 + y^7";
f := eval fString;

PNotLocal<X,Y> := PolynomialRing(R,2);

//##################
//### Curve data
//##################

printf "f = %o\n= %o\n", fString, f;

//prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;
prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^"),i lt#L select", "else"";end for;printf"]";end procedure;


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
printf "\n";



function rhoTilde(ab) // Zhang: rho tilde
	min := Min([Q| offsets[i] + weights[i][1]*ab[1] + weights[i][2]*ab[2] : i in [1..#sides]]);
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
			if j ge 0 then
				Append(~gen, x^i * y^j);
			else
				Append(~gen, x^i);
			end if;
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
		moreGen := &cat[[Pa| fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
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

function HodgeCandidateWithData(k, alpha, rho_to_OTildeGe, allRhos, allHodge, allAlphas)
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
	Ra<a> := RationalFunctionField(R,1);
	Pa := LocalPolynomialRing(Ra,2);
	AssignNames(~Pa, ["x","y"]);
	x := Pa.1;
	y := Pa.2;
	fa := Evaluate(f, [x,y]);
	
	// Õ^{>=rho_i} > Õ^{>=alpha+k} = Õ^{>=rho_{i+1}}
	if alpha + k in allRhos then
		rho := alpha + k;
	else
		rho := Min([Q| rho : rho in allRhos | rho gt alpha + k]);
	end if;
	gen := [Pa| Evaluate(g, [x,y]) : g in rho_to_OTildeGe[rho]];
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeCandidateWithData(k-1, alpha, rho_to_OTildeGe, allRhos, allHodge, allAlphas);
		moreGen := &cat[[Pa| fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
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


function AllHodgeCandidates(kMax)
	assert kMax ge 0;
	
	Ra<a> := RationalFunctionField(R,1);
	Pa := LocalPolynomialRing(Ra,2);
	AssignNames(~Pa, ["x","y"]);
	x := Pa.1;
	y := Pa.2;
	fa := Evaluate(f, [x,y]);
	
	rho_to_OTildeGe := AssociativeArray();
	allRhos := [Q| ];
	rho := rhoTilde([0,0]);
	
	gen := [Pa| Evaluate(g, [x,y]) : g in OTildeGe(rho)];
	rho_to_OTildeGe[rho] := gen;
	Append(~allRhos, rho);
	while rho le (1 + kMax) do
		rhoLast := rho;
		rho +:= 1;
		for l in [1..#gen] do
			ab := Exponents(gen[l]); // x^a*y^b
			r := rhoTilde(ab);
			if r lt rho and r gt rhoLast then rho := r; end if;
			r := rhoTilde([ab[1], ab[2]+1]);
			if r lt rho and r gt rhoLast then rho := r; end if;
			r := rhoTilde([ab[1]+1, ab[2]]);
			if r lt rho and r gt rhoLast then rho := r; end if;
		end for;
		
		gen := [Pa| Evaluate(g, [x,y]) : g in OTildeGe(rho)];
		rho_to_OTildeGe[rho] := gen;
		Append(~allRhos, rho);
	end while;
	print allRhos;
	
	//for rho in allRhos do printf "%o -> ", rho; prt(rho_to_OTildeGe[rho]); printf "\n"; end for;
	allHodge := AssociativeArray();
	allAlphas := [];
	for k in [0..kMax] do
		alphas := [Q| rho + 1 - Ceiling(rho) : rho in allRhos | rho lt k+1];
		Sort(~alphas);
		if 1 notin alphas then Append(~alphas, 1); end if;
		Append(~allAlphas, alphas);
		
		for alpha in alphas do
			gen := HodgeCandidateWithData(k, alpha, rho_to_OTildeGe, allRhos, allHodge, allAlphas);
			ChangeUniverse(~gen, Pa);
			allHodge[<k,alpha>] := gen;
		end for;
	end for;
	/*
	//PaNotLocal := PolynomialRing(R,3);
	//return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	PaNotLocal := PolynomialRing(Ra,2);
	return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	//return gen;
	*/
	//return allRhos, rho_to_OTildeGe;
	
	results := &cat[ [ <k, alpha, allHodge[<k,alpha>]> : alpha in allAlphas[k +1]] : k in [0..kMax]];
	// Remove the correct duplicates (if I1=I2=I3, keep I3)
	results := [ results[i] : i in [1..#results] |
		i eq #results or ideal<Pa|results[i][3]> ne ideal<Pa|results[i+1][3]>];
	
	return results;
end function;




//I := [];
//ILast := I;
//procedure printHodgeCandidate(~I, ~ILast, k, alpha)
//	I := HodgeCandidate(k, alpha);
//	printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
//	Ra<a> := RationalFunctionField(R,1);
//	Pa := LocalPolynomialRing(Ra,2);
//	if ideal<Pa|ILast> eq ideal<Pa|I> then
//		printf "\"\n";
//	else
//		prt(I); printf "\n";
//	end if;
//	ILast := I;
//end procedure;

//O := OTildeGe(3);
//printf "Õ^{>=1} = "; prt(O); printf "\n";

//printHodgeCandidate(~I, ~ILast, 0, 1/21);
//printHodgeCandidate(~I, ~ILast, 0, 10/21);
//printHodgeCandidate(~I, ~ILast, 0, 11/21);
//printHodgeCandidate(~I, ~ILast, 0, 13/21);
//printHodgeCandidate(~I, ~ILast, 0, 16/21);
//printHodgeCandidate(~I, ~ILast, 0, 17/21);
//printHodgeCandidate(~I, ~ILast, 0, 19/21);
//printHodgeCandidate(~I, ~ILast, 0, 20/21);
//printHodgeCandidate(~I, ~ILast, 0, 1);
//print "---";
//printHodgeCandidate(~I, ~ILast, 1, 1/21);
//printHodgeCandidate(~I, ~ILast, 1, 2/21);
//printHodgeCandidate(~I, ~ILast, 1, 4/21);
//printHodgeCandidate(~I, ~ILast, 1, 5/21);
//printHodgeCandidate(~I, ~ILast, 1, 8/21);
//printHodgeCandidate(~I, ~ILast, 1, 10/21);
//printHodgeCandidate(~I, ~ILast, 1, 11/21);
//printHodgeCandidate(~I, ~ILast, 1, 13/21);
//printHodgeCandidate(~I, ~ILast, 1, 16/21);
//printHodgeCandidate(~I, ~ILast, 1, 17/21);
//printHodgeCandidate(~I, ~ILast, 1, 19/21);
//printHodgeCandidate(~I, ~ILast, 1, 20/21);
//printHodgeCandidate(~I, ~ILast, 1, 1);
//print "---";
//printHodgeCandidate(~I, ~ILast, 2, 1/21);


//allRhos, rho_to_OTildeGe := AllHodgeCandidates(1, 1);

h := AllHodgeCandidates(1);
printf "\n";
kLast := 0;
for tup in h do
	k, alpha, I := Explode(tup);
	if k ne kLast then print "---"; end if;
	printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
	prt(I); printf "\n";
	kLast := k;
end for;


printf "\n\nFinished\n";
if quitOnFinish then
	quit;
end if;



