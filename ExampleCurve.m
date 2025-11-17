intrinsic ExampleCurve(G::[RngIntElt]) -> RngPolLocElt, []
	{
		An example of a curve with the given semigroup, and its maximal contact elements.
	}
	error if (not IsPlaneCurveSemiGroup(G)), "Please define a valid plane branch semigroup. Given: ", G;
	
	// Topological information
	planeBranchNumbers := PlaneBranchNumbers(G);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	
	// Choice of equations like Cassou
	n := ns[2..(g+1)]; // ns = [0, n1, ..., ng], n = [n1, ..., ng]
	l := [];
	for s in [1..g] do
		isInG, ls := SemigroupCoordinatesCassouNogues(n[s]*G[s+1], G[(0+1)..(s-1+1)], ns);
		require isInG : Sprintf("n_%o * _beta_%o = %o not in semigroup %o\n", s, s, n[s]*G[s+1], G[(0+1)..(s-1+1)]);
		l[s] := ls[1];
	end for;
	
	// Monomial curve equations
	R := PolynomialRing(RationalField(), G);
	us := [R| R.(i+1) : i in [0..g]];
	//AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
	monomialCurve := [R| us[i +1]^n[i] - Monomial(R, l[i] cat [0 : j in [1..(g+1-#l[i])]]) : i in [1..g]];
	
	// Elimination of the variables u_2,...,u_g, for the curve C1
	C1 := monomialCurve;
	maxContact := [R| us[0+1], us[1+1] ];
	//printf "maxContact = %o\n", maxContact;
	//printf "C1 = %o\n", C1;
	for i in [1..g-1] do
		Append(~maxContact, C1[i]);
		// Evaluate C1 at u_{i+1} and remove top equation
		C1 := [R| Evaluate(h, i+1 +1, -C1[1]) : h in C1[2..#C1]]; 
	end for;
	Append(~maxContact, C1[1]);
	P<x,y> := LocalPolynomialRing(RationalField(),2);
	xyZeros := [P|x,y] cat [P|0:i in [2..g]];
	maxContact := [P| Evaluate(h, xyZeros) : h in maxContact];
	f := maxContact[#maxContact];
	
	return f, maxContact;
end intrinsic;

