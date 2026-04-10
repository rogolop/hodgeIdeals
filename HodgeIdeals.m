//import "SingularitiesDim2/NewtonPolygon.m": NewtonSides;

intrinsic rho_NND_QH(weights::[], ab::[]) -> FldRatElt
{ Weight function for Newton non-degenerate or quasihomogeneous plane curves, applied to the monomial x^a*y^b. }
	min := Min([Rationals()| weights[i][1]*(1 + ab[1]) + weights[i][2]*(1 + ab[2]) : i in [1..#weights]]);
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

intrinsic HodgeIdeal_NND_QH(f::RngMPolLocElt, k::RngIntElt, alpha::FldRatElt) -> []
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
	
	PaNotLocal := PolynomialRing(Ra,2);
	return Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	
	//return gen;
end intrinsic;

intrinsic HodgeIdealWithData_NND_QH(f::RngMPolLocElt, k::RngIntElt, alpha::FldRatElt, rho_to_OGe_NND_QH::Assoc, allRhos::[]) -> []
{ Hodge ideal I_k(f^alpha) for Newton non-degenerate or quasihomogeneous plane curves, given data about OGe_NND_QH. }
	assert k ge 0;
	assert alpha gt 0 and alpha le 1;
	
	Z := Integers();
	Q := Rationals();
	//P := Parent(f);
	//R := BaseRing(P);
	//Ra<a> := RationalFunctionField(R,1);
	//Pa<x,y> := LocalPolynomialRing(Ra,2);
	Pa<x,y> := Universe(rho_to_OGe_NND_QH[allRhos[1]]);
	Ra<a> := BaseRing(Pa);
	fa := Evaluate(f, [x,y]);
	
	// Õ^{>=rho_i} > Õ^{>=alpha+k} = Õ^{>=rho_{i+1}}
	if alpha + k in allRhos then
		rho := alpha + k;
	else
		rho := Min([Q| rho : rho in allRhos | rho gt alpha + k]);
	end if;
	//gen := [Pa| Evaluate(g, [x,y]) : g in rho_to_OGe_NND_QH[rho]];
	gen := rho_to_OGe_NND_QH[rho];
	
	if k gt 0 then
		Hodge_kMinus1 := HodgeIdealWithData_NND_QH(f, k-1, alpha, rho_to_OGe_NND_QH, allRhos);
		moreGen := &cat[[Pa| fa*Pa!Der(g,1) - (a+k-1)*Pa!g*Der(fa,1),
			fa*Pa!Der(g,2) - (a+k-1)*Pa!g*Der(fa,2)] :
			g in Hodge_kMinus1 ];
		gen cat:= moreGen;
	end if;
	
	PaNotLocal := PolynomialRing(Ra,2);
	
	// Prettier basis (no fractions)
	gen := Sort(ChangeUniverse(Reduce(Basis(ideal<PaNotLocal|gen>)), Pa));
	result := [Pa| ];
	for g in gen do
		commonDenomIn_a := LCM([Denominator(c) : c in Coefficients(g)]);
		gPretty := g*commonDenomIn_a;
		commonDenomInteger := LCM(&cat[ [Z| Denominator(cc) : cc in Coefficients(Numerator(c))] : c in Coefficients(gPretty)]);
		gPretty *:= commonDenomInteger;
		Append(~result, gPretty);
	end for;
	return result;
end intrinsic;


intrinsic HodgeIdeals_NND_QH(f::RngMPolLocElt, kMax::RngIntElt) -> []
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
	
	rho_to_OGe_NND_QH := AssociativeArray();
	allRhos := [Q| ];
	rho := rho_NND_QH(weights, [0,0]);
	
	//gen := [Pa| Evaluate(g, [x,y]) : g in OGe_NND_QH(weights, rho, Pa)];
	gen := OGe_NND_QH(weights, rho, Pa);
	rho_to_OGe_NND_QH[rho] := gen;
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
		rho_to_OGe_NND_QH[rho] := gen;
		Append(~allRhos, rho);
	end while;
	
	//for rho in allRhos do printf "%o -> ", rho; prt(rho_to_OGe_NND_QH[rho]); printf "\n"; end for;
	allHodge := AssociativeArray();
	allAlphas := [];
	for k in [0..kMax] do
		alphas := [Q| rho + 1 - Ceiling(rho) : rho in allRhos | rho lt k+1];
		Sort(~alphas);
		if 1 notin alphas then Append(~alphas, 1); end if;
		Append(~allAlphas, alphas);
		
		for alpha in alphas do
			gen := HodgeIdealWithData_NND_QH(f, k, alpha, rho_to_OGe_NND_QH, allRhos);
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
	//return allRhos, rho_to_OGe_NND_QH;
	
	results := &cat[ [ <k, alpha, allHodge[<k,alpha>]> : alpha in allAlphas[k +1]] : k in [0..kMax]];
	// Remove the correct duplicates (if I1=I2=I3, keep I3)
	results := [ results[i] : i in [1..#results] |
		i eq #results or ideal<Pa|results[i][3]> ne ideal<Pa|results[i+1][3]>];
	
	return results;
end intrinsic;



