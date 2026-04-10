AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
Attach("HodgeIdeals.m");
//AttachSpec("ZetaFunction/ZetaFunction.spec");
//Attach("MonomialSequence.m");
//Attach("ExampleCurve.m");
//Attach("planeCurveDiagrams.m");
//import "SingularitiesDim2/IntegralClosure.m": Unloading;
//Z := IntegerRing();
Q := RationalField();

//######################
//### Input/settings
//######################

printDiagrams           := false;
printDiagramsSideBySide := true;
quitOnFinish            := true;

P<x,y>:=LocalPolynomialRing(Q,2);
//PPP<X,Y>:=LocalPolynomialRing(Rationals(),2);
//fString := "(y^2-11*x^3)*(y^3-x^4)";
//fString := "y^3 + x^7";
//fString := "x^3 + y^7";
fString := "x^7+x^4*y^2+y^4";
f := eval fString;


//##################
//### Curve data
//##################

printf "f = %o\n= %o\n", fString, f;

//prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;
//prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^"),i lt#L select", "else"";end for;printf"]";end procedure;
prt:=procedure(L)for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^ "),i lt#L select", "else"";end for;end procedure;

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

//if false then
//	Nf := NewtonPolygon(f); // Points
//	sides := NewtonSides(f, Nf); // For each side: <n, m, F_Gamma(Z)> with n=h(Gamma)
//
//	// Weights for side with slope -n/m, containing point (a,b) in Nf:
//	// (1/m, 1/n) * 1/(a/m + b/n) = ( 1/(a+b*m/n), 1/(a*n/m+b) ) = ( n/(na+mb), m/(na+mb) )
//	weights := []; // Zhang: B_F
//	for i in [1..#sides] do
//		n := sides[i][1];
//		m := sides[i][2];
//		a := Nf[i][1];
//		b := Nf[i][2];
//		Append(~weights, <n/(n*a+m*b), m/(n*a+m*b)>);
//	end for;
//	printf "weights: %o\n", weights;
//	offsets := [ws[1] + ws[2] : ws in weights];
//	printf "offsets: %o\n", offsets;
//	printf "\n";
//end if;



//##################################################
//### Calculate ideals
//##################################################

h := HodgeIdeals_NND_QH(f, 1);
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



