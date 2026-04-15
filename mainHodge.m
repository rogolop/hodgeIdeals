AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
Attach("HodgeIdeals.m");
AttachSpec("ZetaFunction/ZetaFunction.spec"); // -> planeBranchNumbers()
Attach("MonomialSequence.m");
//Attach("ExampleCurve.m");
Attach("planeCurveDiagrams.m");
//import "SingularitiesDim2/IntegralClosure.m": Unloading;
//Z := IntegerRing();
Q := RationalField();

//######################
//### Input/settings
//######################

//SetProfile(true);
printBranchData         := false;
printDiagramsSideBySide := true;
//NND_QH                  := false; // Newton non-degenerate or quasihomogeneous
//branch                  := true;
printMonomialsInMaxCont := false;
quitOnFinish            := true;

kMax := 1;

// Curve type: QH yes, NND no,  branch no
//fString := "(y^3 + x^4)^2"; NND_QH := true; branch := false;

// Curve type: QH no,  NND yes, branch no
//fString := "(y^2-11*x^3)*(y^3-x^4)"; NND_QH := true; branch := false;

// Curve type: QH yes, NND yes, branch yes
//fString := "y^3 + x^7"; NND_QH := true; branch := true;
//fString := "x^3 + y^7"; NND_QH := true; branch := true;
//fString := "y^5 + x^17"; NND_QH := true; branch := true;

// Curve type: QH no,  NND yes, branch yes
fString := "x^7+x^4*y^2+y^4"; NND_QH := true; branch := true;

// Curve type: QH no,  NND no,  branch yes
//fString := "(y^2+x^3)^2 + x^5*y"; NND_QH := false; branch := true;
//fString := "(y^2+x^7)^2 + x^13*y"; NND_QH := false; branch := true;
//fString := "(y^5+x^13)^3 + x^32*y^3"; NND_QH := false; branch := true;

P<x,y>:=LocalPolynomialRing(Q,2);
//PPP<X,Y>:=LocalPolynomialRing(Rationals(),2);
f := eval fString;


//##################
//### Curve data
//##################

printf "f = %o\n= %o\n", fString, f;
printf "NND_QH=%o, branch=%o\n", NND_QH, branch;
printf "\n";

//prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;
//prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^"),i lt#L select", "else"";end for;printf"]";end procedure;
prt:=procedure(L)for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^ "),i lt#L select", "else"";end for;end procedure;

if printBranchData then
	semigroup := SemiGroup(f);
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
	kf := Matrix([[1 : i in [1..numPoints]]]) * PrfTInv;
	M := N; for i in [1..numPoints] do M[i][i] := 0; end for;

	planeBranchNumbers := PlaneBranchNumbers(semigroup);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);

	isFree := [ &+Eltseq(Prf[pt]) ge 0 : pt in [1..numPoints]];
	isRupture := [ (&+Eltseq(M[pt]) ge 3) or (pt eq numPoints and &+Eltseq(M[pt]) ge 2) : pt in [1..numPoints]];
	isMaxContact := [ (pt eq 1) or (isFree[pt] and (pt lt numPoints) and not isFree[pt+1]) : pt in [1..numPoints]];

	printf "Semigroup: %o\n", semigroup;
	printf "\n";

	diagramData := diagramDataFromProximity(Prf); // For plots

	printf "Points:\n";
	annotations := [Sprintf("p%o", pt-1) : pt in [1..numPoints]];
	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	printf "Multiplicities:\n";
	annotations := ef[1];
	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	printf "Values:\n";
	annotations := vf[1];
	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	printf "Canonical:\n";
	annotations := kf[1];
	printAnnotatedEnriquesDiagramAndDualGraph(diagramData, annotations : sideBySide:=printDiagramsSideBySide);
	printf "\n";

	if NND_QH then
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
	else
		//print &cat[Sprintf("p%o ", pt-1) : pt in [1..numPoints] | isMaxContact[pt]];
		//printf "\n";
	end if;

	printf "Max contact: "; prt(MaxContactElements(f)); printf "\n\n";
end if;


//##################################################
//### Hodge ideals
//##################################################


if NND_QH then
	h_NND_QH := HodgeIdeals_NND_QH(f, kMax);
	kLast := 0;
	for tup in h_NND_QH do
		k, alpha, I := Explode(tup);
		if k ne kLast then print "---"; end if;
		printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
		prt(I); printf "\n";
		kLast := k;
	end for;
	if branch then
		print "====================";	
		printf "\nImplementations give equal results?\n";
		h_branch := HodgeIdeals_branch(f, kMax);
		if #h_NND_QH ne #h_branch then
			printf "false\n";
		else
			equal := true;
			for i in [1..#h_branch] do
				if h_NND_QH[i][1] ne h_branch[i][1] or
					h_NND_QH[i][2] ne h_branch[i][2] or
					h_NND_QH[i][3] ne ChangeUniverse(h_branch[i][3], Universe(h_NND_QH[i][3]))
				then
					equal := false;
					printf "false: %o\n", i;
					prt(h_branch[i][3]); printf "\n";
					
				end if;
			end for;
			if equal then printf "true\n"; end if;
		end if;
	end if;
else
	h_branch := HodgeIdeals_branch(f, kMax : reduceBasis:=true);
	Pa := Universe(h_branch[1][3]);
	maxContact := [Pa| Evaluate(h, [x,y]) : h in MaxContactElements(f) cat [f]];
	kLast := 0;
	for tup in h_branch do
		k, alpha, I := Explode(tup);
		if k ne kLast then print "===================="; end if;
			printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
			if printMonomialsInMaxCont then
			S, extra := MonomialSequence(I, maxContact);
			printf"[";for i->l in S do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#S select", "else"";end for;printf"]";printf"\n";
			if #extra gt 0 then
				for i->g in extra do
					printf "g%o= %o\n", i, g;
				end for;
				printf "\n";
			end if;
		else
			prt(I); printf "\n";
		end if;
		kLast := k;
	end for;
end if;


printf "\n\nFinished\n";
//SetProfile(false);
//G := ProfileGraph();
//V := Vertices(G);
//ProfilePrintByTotalTime(G : Max:=20);
//printf "\n";
//ProfilePrintChildrenByTime(G,8 : Max:=20);

if quitOnFinish then
	quit;
end if;



