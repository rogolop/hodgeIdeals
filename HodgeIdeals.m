//import "SingularitiesDim2/NewtonPolygon.m": NewtonSides;

prt:=procedure(L)for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*^ "),i lt#L select", "else"";end for;end procedure;

intrinsic rho_NND_QH(weights::[], ab::[]) -> FldRatElt
{ Weight function for Newton non-degenerate or quasihomogeneous plane curves, applied to the monomial x^a*y^b. }
	min, _ := Min([Rationals()| weights[i][1]*(1 + ab[1]) + weights[i][2]*(1 + ab[2]) : i in [1..#weights]]);
	return min;
end intrinsic;

intrinsic OGe_NND_QH(weights::[], rho::FldRatElt, Pa::RngMPolLoc) -> []
{ Monomial generators with weight >= rho, for Newton non-degenerate or quasihomogeneous plane curves. }
	x := Pa.1; y := Pa.2;
	
	j := 0;
	while rho_NND_QH(weights, [0,j]) lt rho do
		j +:= 1;
	end while;
	gen := [Pa| y^j];
	i := 1;
	jLast := j;
	while j gt 0 do
		jLast := j;
		while rho_NND_QH(weights, [i,j]) ge rho do
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
end intrinsic;

intrinsic Der(f::RngMPolLocElt, i::RngIntElt) -> RngMPolLocElt
{ Derivative of f with respect to the i-th variable in a local polynomial ring. }
	P := Parent(f);
	df := P!0;
	for t in Terms(f) do
		d := Degree(t,i);
		if d gt 0 then
			df +:= d * Evaluate(t, i, 1) * P.i^(d-1);
		end if;
	end for;
	return df;
end intrinsic;

intrinsic HodgeIdeal_NND_QH(f::RngMPolLocElt, k::RngIntElt, alpha::FldRatElt : reduceBasis:=true, clearDenominators:=true) -> []
{ Hodge ideal I_k(f^alpha) for Newton non-degenerate or quasihomogeneous plane curves. }
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
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
	
	P := Parent(f);
	R := BaseRing(P);
	Ra<a> := RationalFunctionField(R,1);
	Pa<x,y> := LocalPolynomialRing(Ra,2);
	//AssignNames(~Pa, ["x","y"]); x := Pa.1; y := Pa.2;
	fa := Evaluate(f, [x,y]);
	//gen := [Pa| Evaluate(g, [x,y]) : g in OGe_NND_QH(weights, alpha + k, Pa)];
	gen := OGe_NND_QH(weights, alpha + k, Pa);
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeIdeal_NND_QH(f, k-1, alpha);
		moreGen := &cat[[Pa| fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
			fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2)] :
			g in Hodge_kMinus1 ];
		gen cat:= moreGen;
	end if;
	
	// Prettier basis
	Z := Integers();
	if reduceBasis then
		PaNotLocal := PolynomialRing(Ra,2);
		gen := Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	end if;
	if clearDenominators then
		result := [Pa| ];
		for g in gen do
			commonDenomIn_a := LCM([Denominator(c) : c in Coefficients(g)]);
			gPretty := g * commonDenomIn_a;
			commonDenomInteger := LCM(&cat[ [Z| Denominator(cc) : cc in Coefficients(Numerator(c))] : c in Coefficients(gPretty)]);
			gPretty *:= commonDenomInteger;
			Append(~result, gPretty);
		end for;
		return result;
	else
		return gen;
	end if;

	//return gen;
end intrinsic;

intrinsic HodgeIdealWithData_NND_QH(f::RngMPolLocElt, k::RngIntElt, alpha::FldRatElt, rho_to_OGe::Assoc, allRhos::[] : reduceBasis:=true, clearDenominators:=true, extraInfo:=false) -> []
{ Hodge ideal I_k(f^alpha) for Newton non-degenerate or quasihomogeneous plane curves, given data about OGe_NND_QH. }
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
	Z := Integers();
	Q := Rationals();
	//P := Parent(f);
	//R := BaseRing(P);
	//Ra<a> := RationalFunctionField(R,1);
	//Pa<x,y> := LocalPolynomialRing(Ra,2);
	Pa<x,y> := Universe(rho_to_OGe[allRhos[1]]);
	Ra<a> := BaseRing(Pa);
	fa := Evaluate(f, [x,y]);
	
	// Õ^{>=rho_i} > Õ^{>=alpha+k} = Õ^{>=rho_{i+1}}
	rho := Min([Q| rho : rho in allRhos | rho ge alpha + k]);
	
	//gen := [Pa| Evaluate(g, [x,y]) : g in rho_to_OGe[rho]];
	OGe := rho_to_OGe[rho];
	gen := OGe;
	fI_kMinus1 := [Pa| ];
	derGenI_kMinus1 := [Pa| ];
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeIdealWithData_NND_QH(f, k-1, alpha, rho_to_OGe, allRhos);
		ChangeUniverse(~Hodge_kMinus1, Pa);
		fI_kMinus1 := [Pa| fa*g : g in Hodge_kMinus1];
		derGenI_kMinus1 := [Pa| 0 : i in [1..(2*#Hodge_kMinus1)]];
		for i->g in Hodge_kMinus1 do
			derGenI_kMinus1[2*i-1] := fa*Der(g,1) - (a+k-1)*g*Der(fa,1);
			derGenI_kMinus1[2*i]   := fa*Der(g,2) - (a+k-1)*g*Der(fa,2);
		end for;
		gen cat:= fI_kMinus1;
		gen cat:= derGenI_kMinus1;
	end if;
	
	// Prettier basis
	if reduceBasis then
		PaNotLocal := PolynomialRing(Ra,2);
		gen := Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	end if;
	if clearDenominators then
		result := [Pa| ];
		for g in gen do
			commonDenomIn_a := LCM([Denominator(c) : c in Coefficients(g)]);
			gPretty := g * commonDenomIn_a;
			commonDenomInteger := LCM(&cat[ [Z| Denominator(cc) : cc in Coefficients(Numerator(c))] : c in Coefficients(gPretty)]);
			gPretty *:= commonDenomInteger;
			Append(~result, gPretty);
		end for;
		return result, OGe, fI_kMinus1, derGenI_kMinus1;
	else
		return gen, OGe, fI_kMinus1, derGenI_kMinus1;
	end if;
end intrinsic;


intrinsic HodgeIdeals_NND_QH(f::RngMPolLocElt, kMax::RngIntElt : reduceBasis:=true, clearDenominators:=true, extraInfo:=false) -> []
{ Hodge ideals I_k(f^alpha) for all 0<=k<=kMax and all 0<alpha<=1, for Newton non-degenerate or quasihomogeneous plane curves. }
	assert kMax ge 0;
	
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
		//Append(~weights, <n/(n*a+m*b), m/(n*a+m*b)>);
		Append(~weights, <1/m /(a/m + b/n), 1/n /(a/m + b/n)>);
	end for;
	
	Q := Rationals();
	P := Parent(f);
	R := BaseRing(P);
	Ra<a> := RationalFunctionField(R,1);
	Pa<x,y> := LocalPolynomialRing(Ra,2);
	fa := Evaluate(f, [x,y]);
	
	rho_to_OGe := AssociativeArray();
	allRhos := [Q| ];
	rho := rho_NND_QH(weights, [0,0]);
	
	//gen := [Pa| Evaluate(g, [x,y]) : g in OGe_NND_QH(weights, rho, Pa)];
	gen := OGe_NND_QH(weights, rho, Pa);
	rho_to_OGe[rho] := gen;
	Append(~allRhos, rho);
	while rho le (1 + kMax) do
		// The next rho is the minimum value of rho_NND_QH() greater than rho
		rhoNext := rho+1; // upper bound of the next rho
		for l in [1..#gen] do
			a, b := Explode(Exponents(gen[l])); // x^a*y^b
			r := rho_NND_QH(weights, [a,b]);
			if r gt rho and r lt rhoNext then rhoNext := r; end if;
			r := rho_NND_QH(weights, [a, b+1]);
			if r gt rho and r lt rhoNext then rhoNext := r; end if;
			r := rho_NND_QH(weights, [a+1, b]);
			if r gt rho and r lt rhoNext then rhoNext := r; end if;
		end for;
		rho := rhoNext;
		
		//gen := [Pa| Evaluate(g, [x,y]) : g in OGe_NND_QH(weights, rho, Pa)];
		gen := OGe_NND_QH(weights, rho, Pa);
		rho_to_OGe[rho] := gen;
		Append(~allRhos, rho);
	end while;
	
	//for rho in allRhos do printf "%o: ", rho; prt(rho_to_OGe[rho]); printf "\n"; end for;
	
	allHodge := AssociativeArray();
	allAlphas := [];
	allExtra := AssociativeArray();
	for k in [0..kMax] do
		alphas := [Q| rho + 1 - Ceiling(rho) : rho in allRhos | rho lt k+1];
		Sort(~alphas);
		if 1 notin alphas then Append(~alphas, 1); end if;
		Append(~allAlphas, alphas);
		
		for alpha in alphas do
			if extraInfo then
				gen, OGe, fI_kMinus1, derGenI_kMinus1 := HodgeIdealWithData_NND_QH(f, k, alpha, rho_to_OGe, allRhos : reduceBasis:=reduceBasis, clearDenominators:=clearDenominators, extraInfo:=true);
				//ChangeUniverse(~gen, Pa);
				allHodge[<k,alpha>] := gen;
				allExtra[<k,alpha>] := [OGe, fI_kMinus1, derGenI_kMinus1];
			else
				gen := HodgeIdealWithData_NND_QH(f, k, alpha, rho_to_OGe, allRhos : reduceBasis:=reduceBasis, clearDenominators:=clearDenominators, extraInfo:=false);
				//ChangeUniverse(~gen, Pa);
				allHodge[<k,alpha>] := gen;
			end if;
		end for;
	end for;
	/*
	//PaNotLocal := PolynomialRing(R,3);
	//return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	PaNotLocal := PolynomialRing(Ra,2);
	return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	//return gen;
	*/
	//return allRhos, rho_to_OGe;
	
	results := &cat[ [ <k, alpha, allHodge[<k,alpha>]> : alpha in allAlphas[k +1]] : k in [0..kMax]];
	// Remove the correct duplicates (if I1=I2=I3, keep I3)
	results := [ results[i] : i in [1..#results] |
		i eq #results or ideal<Pa|results[i][3]> ne ideal<Pa|results[i+1][3]>];
	
	if extraInfo then
		return results, allExtra;
	else
		return results;
	end if;
end intrinsic;


intrinsic rho_branch(weightsData::<>, exponents::[]) -> FldRatElt
{ Weight function for plane branches, applied to the product of maximal contact elements with the given exponents. }
	g, Nps, kps, valuesMaxContact := Explode(weightsData);
	//Q := Rationals();
	
	//values := [Q|
	//	&+[Q| exponents[j +1] * valuesMaxContact[j +1][pt] : j in [0..g]]
	//: pt in [1..g]];
	//min, _ := Min([Q| (values[pt] + kps[pt] + 1)/(Nps[pt]) : pt in [1..g]]);
	
	//values := [Q| 0 : pt in [1..g]];
	//for pt in [1..g] do
	//	for j in [1..g+1] do
	//		values[pt] +:= exponents[j] * valuesMaxContact[j][pt];
	//	end for;
	//end for;
	
	//min := (values[1] + kps[1] + 1)/(Nps[1]);
	//for pt in [2..g] do
	//	new := (values[pt] + kps[pt] + 1)/(Nps[pt]);
	//	if new lt min then min := new; end if;
	//end for;
	
	value := exponents[1] * valuesMaxContact[1][1];
	for j in [2..g+1] do
		value +:= exponents[j] * valuesMaxContact[j][1];
	end for;
	min := (value + kps[1] + 1)/(Nps[1]);
	for pt in [2..g] do
		value := exponents[1] * valuesMaxContact[1][pt];
		for j in [2..g+1] do
			value +:= exponents[j] * valuesMaxContact[j][pt];
		end for;
		value := (value + kps[pt] + 1)/(Nps[pt]);
		if value lt min then min := value; end if;
	end for;
	return min;
end intrinsic;


intrinsic NextOGeExp_branch(genExpPrev::[], weightsData::<>, rho::FldRatElt) -> []
{ Monomial generators with weight >= rho, for plane branches, given. }
	g := weightsData[1];
	genExp := {};
	pending := {};
	moreGen := {};
	//printf "genExp=%o\n", genExp;
	for exponents in genExpPrev do
		r := rho_branch(weightsData, exponents);
		if r ge rho then
			Include(~genExp, exponents);
		else
			for i in [0..g] do
				exp := exponents;
				exp[i +1] +:= 1;
				Include(~pending, exp);
			end for;
		end if;
	end for;
	//printf "pending=%o\n", pending;
	for exponents in pending do
		deleted := false;
		for gen in genExp do
			unnecessary := true;
			for j in [1..g+1] do
				if exponents[j] lt gen[j] then
					unnecessary := false;
					break;
				end if;
			end for;
			if unnecessary then
				deleted := true;
				break;
			end if;
		end for;
		if not deleted then
			Include(~moreGen, exponents);
		end if;
	end for;
	pending := moreGen;
	//printf "pending=%o\n", pending;
	for exponents in pending do
		deleted := false;
		for gen in moreGen do
			if gen eq exponents then continue; end if;
			unnecessary := true;
			for j in [1..g+1] do
				if exponents[j] lt gen[j] then
					unnecessary := false;
					break;
				end if;
			end for;
			if unnecessary then
				deleted := true;
				break;
			end if;
		end for;
		if deleted then
			Exclude(~moreGen, exponents);
		end if;
	end for;
	//printf "moreGen=%o\n\n", moreGen;
	return [ exp : exp in genExp ] cat [ exp : exp in moreGen ];
end intrinsic;


intrinsic ExponentsToElement(maxContact::[], exponents::[]) -> RngMPolLocElt
{}
	//return &*[maxContact[i]^(exponents[i]) : i in [1..#maxContact]];
	elt := maxContact[1]^(exponents[1]);
	for i in [2..#maxContact] do
		elt *:= maxContact[i]^(exponents[i]);
	end for;
	return elt;
end intrinsic


intrinsic HodgeIdealWithData_branch(f::RngMPolLocElt, k::RngIntElt, alpha::FldRatElt, rho_to_OGeExp::Assoc, allRhos::{}, maxContact::[] : reduceBasis:=true, clearDenominators:=true, extraInfo:=false) -> []
{ Hodge ideal I_k(f^alpha) for plane branches, given data about OGe. }
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
	Z := Integers();
	Q := Rationals();
	Pa<x,y> := Universe(maxContact);
	Ra<a> := BaseRing(Pa);
	fa := Evaluate(f, [x,y]);
	
	// Õ^{>=rho_i} > Õ^{>=alpha+k} = Õ^{>=rho_{i+1}}
	rho := Min({Q| rho : rho in allRhos | rho ge alpha + k});
	
	OGe := [Pa| ExponentsToElement(maxContact, exponents) : exponents in rho_to_OGeExp[rho]];
	gen := OGe;
	fI_kMinus1 := [Pa| ];
	derGenI_kMinus1 := [Pa| ];
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeIdealWithData_branch(f, k-1, alpha, rho_to_OGeExp, allRhos, maxContact);
		ChangeUniverse(~Hodge_kMinus1, Pa);
		fI_kMinus1 := [Pa| fa*g : g in Hodge_kMinus1];
		derGenI_kMinus1 := [Pa| 0 : i in [1..(2*#Hodge_kMinus1)]];
		for i->g in Hodge_kMinus1 do
			derGenI_kMinus1[2*i-1] := fa*Der(g,1) - (a+k-1)*g*Der(fa,1);
			derGenI_kMinus1[2*i]   := fa*Der(g,2) - (a+k-1)*g*Der(fa,2);
		end for;
		gen cat:= fI_kMinus1;
		gen cat:= derGenI_kMinus1;
		//moreGen := &cat[[Pa| fa*Pa!g, fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
		//	fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2)] :
		//	g in Hodge_kMinus1 ];
			
		//moreGen := [Pa| fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1)
		//	: g in Hodge_kMinus1 ] cat
		//	[Pa| fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2)
		//	: g in Hodge_kMinus1 ];
			
		//moreGen := [Pa| 0 : i in [1..2*#Hodge_kMinus1]];
		//for i in [1..#Hodge_kMinus1] do
		//	g := Hodge_kMinus1[i];
		//	moreGen[2*i] := fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1);
		//	moreGen[2*i+1] := fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2);
		//end for;
		//gen cat:= moreGen;
	end if;
	
	// Prettier basis
	if reduceBasis then
		PaNotLocal := PolynomialRing(Ra,2);
		gen := Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	end if;
	if clearDenominators then
		result := [Pa| 0 : g in gen];
		for i->g in gen do
			commonDenomIn_a := LCM({Denominator(c) : c in Coefficients(g)});
			gPretty := g * commonDenomIn_a;
			commonDenomInteger := LCM({Z| Denominator(cc) : cc in Coefficients(Numerator(c)), c in Coefficients(gPretty)});
			gPretty *:= commonDenomInteger;
			//Append(~result, gPretty);
			result[i] := gPretty;
		end for;
		return result, OGe, fI_kMinus1, derGenI_kMinus1;
	else
		return gen, OGe, fI_kMinus1, derGenI_kMinus1;
	end if;
end intrinsic;


intrinsic HodgeIdeals_branch(f::RngMPolLocElt, kMax::RngIntElt : reduceBasis:=true, clearDenominators:=true, extraInfo:=false) -> []
{ Hodge ideals I_k(f^alpha) for all 0<=k<=kMax and all 0<alpha<=1, for plane branches. }
	assert kMax ge 0;
	
	Z := Integers();
	Q := Rationals();
	semigroup := SemiGroup(f);
	g := #semigroup -1;
	planeBranchNumbers := PlaneBranchNumbers(semigroup);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	// j -> which maximal contact element (0:x, 1:y, ..., g:...)
	// i -> which rupture point (1..g)
	valuesMaxContact :=
	[
		[Q| ns[i +1] * _betas[i +1] / es[j-1 +1] : i in [1..j-1]]
		cat
		[Q| _betas[j +1] / es[i +1] : i in [Max(1,j)..g]]
	: j in [0..g]];
	weightsData := <g, Nps, kps, valuesMaxContact>;
	//weights := [ Min([(valuesMaxContact[j +1][i] + kps[i] + 1)/(Nps[i]) : i in [1..g]]) : j in [0..g]];
	
	//printf "weights = %o\n", weightsData;
	
	P := Parent(f);
	R := BaseRing(P);
	Ra<a> := RationalFunctionField(R,1);
	Pa<x,y> := LocalPolynomialRing(Ra,2);
	fa := Evaluate(f, [x,y]);
	
	maxContact := [Pa| Evaluate(h, [x,y]) : h in MaxContactElements(f)];
	
	rho_to_OGeExp := AssociativeArray();
	allRhos := {Q| };
	
	genExp := [ [Z| 0 : i in [0..g]] ];
	rho := rho_branch(weightsData, genExp[1]);
	rho_to_OGeExp[rho] := genExp;
	Include(~allRhos, rho);
	while rho le (1 + kMax) do
		// The next rho is the minimum value of rho_branch() greater than rho
		rhoNext := rho+1; // upper bound of the next rho
		for exponents in genExp do
			r := rho_branch(weightsData, exponents);
			if r gt rho and r lt rhoNext then rhoNext := r; end if;
			for i in [0..g] do
				exp := exponents;
				exp[i +1] +:= 1;
				r := rho_branch(weightsData, exp);
				if r gt rho and r lt rhoNext then rhoNext := r; end if;
			end for;
		end for;
		rho := rhoNext;
		
		genExp := NextOGeExp_branch(genExp, weightsData, rho);
		rho_to_OGeExp[rho] := genExp;
		Include(~allRhos, rho);
	end while;
	
	//for rho in allRhos do printf "%o: ", rho; prt([ExponentsToElement(maxContact,h) : h in rho_to_OGeExp[rho]]); printf "\n"; end for;
	
	allHodge := AssociativeArray();
	allAlphas := [];
	allExtra := AssociativeArray();
	for k in [0..kMax] do
		alphas := [Q| rho + 1 - Ceiling(rho) : rho in allRhos | rho lt k+1];
		Sort(~alphas);
		if 1 notin alphas then Append(~alphas, 1); end if;
		Append(~allAlphas, alphas);
		
		for alpha in alphas do
			allHodge[<k,alpha>] := HodgeIdealWithData_branch(f, k, alpha, rho_to_OGeExp, allRhos, maxContact : reduceBasis:=reduceBasis, clearDenominators:=clearDenominators);
			
			if extraInfo then
				gen, OGe, fI_kMinus1, derGenI_kMinus1 := HodgeIdealWithData_branch(f, k, alpha, rho_to_OGeExp, allRhos, maxContact : reduceBasis:=reduceBasis, clearDenominators:=clearDenominators, extraInfo:=true);
				//ChangeUniverse(~gen, Pa);
				allHodge[<k,alpha>] := gen;
				allExtra[<k,alpha>] := [OGe, fI_kMinus1, derGenI_kMinus1];
			else
				gen := HodgeIdealWithData_branch(f, k, alpha, rho_to_OGeExp, allRhos, maxContact : reduceBasis:=reduceBasis, clearDenominators:=clearDenominators, extraInfo:=false);
				//ChangeUniverse(~gen, Pa);
				allHodge[<k,alpha>] := gen;
			end if;
		end for;
	end for;
	
	results := [ <k, alpha, allHodge[<k,alpha>]> : alpha in allAlphas[k +1], k in [0..kMax]];
	
	// Remove the correct duplicates (if I1=I2=I3, keep I3)
	//results := [];
	//for i->tup in tuples do
	//	if i eq #tuples then
	//		Append(~results, tup);
	//	else
	//		nextIdeal := ideal<Pa|tuples[i+1][3]>;
	//		different := false;
	//		for gen in tup[3] do
	//			if gen notin nextIdeal then
	//				different := true;
	//				break;
	//			end if;
	//		end for;
	//		if different then
	//			Append(~results, tup);
	//		end if;
	//	end if;
	//end for;
	
	results := [ results[i] : i in [1..#results] |
		i eq #results or ideal<Pa|results[i][3]> ne ideal<Pa|results[i+1][3]>];
	
	//ideals := [ ideal<Pa|tup[3]> : tup in results ];
	//results := [ results[i] : i in [1..#results] |
	//	i eq #results or ideals[i] notsubset ideals[i+1]];
	
	if extraInfo then
		return results, allExtra;
	else
		return results;
	end if;
	
	//chosen := [false : i in [1..#results]];
	//ideal := Pa;
	//nextIdeal := Pa;
	//for i in [1..#results] do
	//	if i eq #results then
	//		chosen[i] := true;
	//	else
	//		if i eq 1 then
	//			ideal := ideal<Pa|results[i][3]>;
	//		else
	//			ideal := nextIdeal;
	//		end if;
	//		nextIdeal := ideal<Pa|results[i+1][3]>;
	//		//for gen in results[i][3] do
	//		//	if gen notin nextIdeal then
	//		//		chosen[i] := true;
	//		//		break;
	//		//	end if;
	//		//end for;
	//		if ideal ne nextIdeal then
	//			chosen[i] := true;
	//		end if;
	//	end if;
	//end for;
	//return [ res : i->res in results | chosen[i] ];
end intrinsic;



