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
printMonomialsInMaxCont := false;
extraInfo               := false;
printIntegralClosure    := false;
printHodge              := true;
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
//fString := "x^7+y^4"; NND_QH := true; branch := true;
//fString := "y^5 + x^6"; NND_QH := true; branch := true;

// Curve type: QH no,  NND yes, branch yes
fString := "x^7+x^4*y^2+y^4"; NND_QH := true; branch := true;
//fString := "y^5 + x^17 + x^15*y"; NND_QH := true; branch := true;

// Curve type: QH no,  NND no,  branch yes
//fString := "(y^2+x^3)^2 + x^5*y"; NND_QH := false; branch := true;
//fString := "(y^2+x^7)^2 + x^13*y"; NND_QH := false; branch := true;
//fString := "(y^5+x^13)^3 + x^32*y^3"; NND_QH := false; branch := true;
//fString := "(x^3-y^2)^5 -x^18"; NND_QH := false; branch := true;

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

function substringSubstitution(string, substring, substitute)
	newString := "";
	n := #string;
	l := #substring;
	i := 1;
	while i le (n-l+1) do
		if string[i..(i+l-1)] eq substring then
			newString cat:= substitute;
			i +:= l;
		else
			newString cat:= string[i];
			i +:= 1;
		end if;
	end while;
	newString cat:= string[i..n];
	return newString;
end function;

procedure prt2Impl(prefix, L, maxContact)
	printf prefix;
	if printMonomialsInMaxCont then
		S, extra := MonomialSequence(L, maxContact);
		//printf"[";
		for i->l in S do
			string := Sprintf("%o",l);
			string := &cat Split(string,"*");
			string := substringSubstitution(string, "x^", "x");
			string := substringSubstitution(string, "y^", "y");
			string := substringSubstitution(string, "a^", "a");
			printf "%o%o", string, i lt#S select", "else"";
		end for;
		//printf"]";
		printf"\n";
		if #extra gt 0 then
			for i->g in extra do
				//printf "g%o= %o\n", i, g;
				printf "g%o= ", i; prt([g]); printf "\n";
			end for;
			printf "\n";
		end if;
	else
		prt(L); printf "\n";
	end if;
end procedure;

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
	if extraInfo then
		h_NND_QH, extra := HodgeIdeals_NND_QH(f, kMax : reduceBasis:=true, clearDenominators:=true, extraInfo:=true);
	else
		h_NND_QH := HodgeIdeals_NND_QH(f, kMax : reduceBasis:=true, clearDenominators:=true, extraInfo:=false);
	end if;
	h := h_NND_QH;
	
	Pa := Universe(h[1][3]);
	maxContact := [Pa| Evaluate(h, [x,y]) : h in MaxContactElements(f) cat [f]];
	prt2 := procedure(prefix,L)prt2Impl(prefix,L,maxContact);end procedure;
	if printHodge then
		kLast := 0;
		for tup in h_NND_QH do
			k, alpha, I := Explode(tup);
			if k ne kLast then print "---"; end if;
			//printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
			//prt(I); printf "\n";
			prt2(Sprintf("%-16o",Sprintf("I_%o(f^%o): ",k,alpha)), I);
			
			//h_discard := HodgeIdeal_NND_QH(f, k, alpha);
			//print I eq ChangeUniverse(h_discard, Universe(I));
			//printf "\n";
			if extraInfo then
				prt2("OGe:            ", extra[<k,alpha>][1]);
				prt2("fIkMinus1:      ", extra[<k,alpha>][2]);
				prt2("derGenIkMinus1: ", extra[<k,alpha>][3]);
				printf "\n";
			end if;
			
			if printIntegralClosure then
				Pa := Universe(I);
				I := ideal<Pa| I>;
				Icl := IntegralClosure(I);
				Icl := ideal<Pa| Icl>;
				if I eq Icl then
					printf "Integrally closed\n";
				else
					printf "Integral closure: ";
					prt(Basis(Icl));
					printf "\n";
					P, v := LogResolution(Icl);
					print P;
					printf "v(int.cl.) = %o\n", v;
				end if;
				printf "\n";
			end if;

			kLast := k;
		end for;
		printf "\n";
	end if;
	if branch then
		printf "Implementations give equal results?\n";
		h_branch := HodgeIdeals_branch(f, kMax);
		if #h_NND_QH ne #h_branch then
			printf "false: different number of ideals\n\n";
		Pa := Universe(h[1][3]);
		maxContact := [Pa| Evaluate(h, [x,y]) : h in MaxContactElements(f) cat [f]];
		prt2 := procedure(prefix,L)prt2Impl(prefix,L,maxContact);end procedure;
		else
			equal := true;
			for i in [1..#h_branch] do
				if h_NND_QH[i][1] ne h_branch[i][1] or
					h_NND_QH[i][2] ne h_branch[i][2] or
					h_NND_QH[i][3] ne ChangeUniverse(h_branch[i][3], Universe(h_NND_QH[i][3]))
				then
					equal := false;
					printf "false:\n";
					printf "I_NND_QH_%o(f^%o) = ", h_NND_QH[i][1], h_NND_QH[i][2]; prt(h_NND_QH[i][3]); printf "\n";
					printf "I_branch_%o(f^%o) = ", h_NND_QH[i][1], h_NND_QH[i][2]; prt(h_branch[i][3]); printf "\n\n";
					
				end if;
			end for;
			if equal then printf "true\n\n"; end if;
		end if;
	end if;
else
	if extraInfo then
		h_branch, extra := HodgeIdeals_branch(f, kMax : reduceBasis:=true, clearDenominators:=true, extraInfo:=true);
	else
		h_branch := HodgeIdeals_branch(f, kMax : reduceBasis:=true, clearDenominators:=true, extraInfo:=false);
	end if;
	h := h_branch;
	
	Pa := Universe(h[1][3]);
	maxContact := [Pa| Evaluate(h, [x,y]) : h in MaxContactElements(f) cat [f]];
	prt2 := procedure(prefix,L)prt2Impl(prefix,L,maxContact);end procedure;
	if printHodge then
		kLast := 0;
		for tup in h_branch do
			k, alpha, I := Explode(tup);
			if k ne kLast then print "---";; end if;
			//printf "%-16o", Sprintf("I_%o(f^%o): ", k, alpha);
			//if printMonomialsInMaxCont then
			//	S, extra := MonomialSequence(I, maxContact);
			//	printf"[";for i->l in S do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#S select", "else"";end for;printf"]";printf"\n";
			//	if #extra gt 0 then
			//		for i->g in extra do
			//			printf "g%o= %o\n", i, g;
			//		end for;
			//		printf "\n";
			//	end if;
			//else
			//	prt(I); printf "\n";
			//end if;
			prt2(Sprintf("%-16o",Sprintf("I_%o(f^%o): ",k,alpha)), I);
			
			if extraInfo then
				prt2("OGe:            ", extra[<k,alpha>][1]);
				prt2("fIkMinus1:      ", extra[<k,alpha>][2]);
				prt2("derGenIkMinus1: ", extra[<k,alpha>][3]);
				printf "\n";
			end if;
			
			if printIntegralClosure then
				Pa := Universe(I);
				I := ideal<Pa| I>;
				Icl := IntegralClosure(I);
				Icl := ideal<Pa| Icl>;
				if I eq Icl then
					printf "Integrally closed\n";
				else
					printf "Integral closure: ";
					prt(Basis(Icl));
					printf "\n";
					P, v := LogResolution(Icl);
					print P;
					printf "v(int.cl.) = %o\n", v;
				end if;
				printf "\n";
			end if;
			
			kLast := k;
		end for;
		printf "\n";
	end if;
end if;

printf "Multipliers coincide up to 1?\n";
Js := MultiplierIdeals(f); // : MaxJN:=1
h := [ h[i] : i in [1..#Js] ]; // k=0 and first k=1
Pa := Universe(h[1][3]);

equal := true;
for i in [2..#Js] do
	if i lt #Js and h[i][2] ne Js[i+1][2] then
		printf "false: Different jumping number: Hodge %o, multipliers %o\n", h[i][2], Js[i+1][2];
		equal := false;
	elif ideal<Pa| h[i][3]> ne ideal<Pa| Js[i][1]> then
		printf "false: Different ideals: alpha = %o\n", h[i][2];
		printf "I = "; prt(h[i][3]); printf "\n";
		printf "J = "; prt(Js[i][1]); printf "\n";
		equal := false;
	end if;
end for;
if equal then printf "true\n"; end if;



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



