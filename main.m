AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Attach("MonomialSequence.m");
Z := IntegerRing();
Q := RationalField();
prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]\n";end procedure;

R := Q;
P<x,y> := LocalPolynomialRing(R,2);
f := (y^2-x^3)^5 + x^18; // 10-15-36
maxContact := [P| x, y, y^2-x^3, f ];

//f := y^6 - x^7;
//f := x^5 + y^5 + x^2*y^2;

mu := MilnorNumber(f);
printf "\nSemigroup %o\n", SemiGroup(f);
printf "mu=%o\n", mu;
printf "f = %o\n", f;
printf "\n";

// Calculate
filtration := Filtration(f : N:=mu);
multipliers := MultiplierIdeals(f);
//filtrationRup := FiltrationRupture(f,1);

// Prepare

//print Universe(filtration[1][1]);
filtration := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration];
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


// Compare

print "Columns:";
print "- Filtration ideal is a multiplier ideal (y/NO)";
print "- Intersection multiplicity of the clusters?";
print "- Jumping number, or ideal that is not a multiplier ideal";
printf "\n";

multiplierIdealsCopy := multiplierIdeals;
for I in filtrationIdeals do
	if I in multiplierIdealsCopy then
		printf "   Y %-4o %o\n", filtrationIdealToInt[I], multiplierIdealToJN[I];
		Exclude(~multiplierIdealsCopy, I);
	else
		printf "NO   %-4o ", filtrationIdealToInt[I];
		if false then
			//IndentPush();
			SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
			prt(SNice); for i->elt in extras do printf "g%o = %o\n", i, elt; end for;
			//IndentPop();
		end if;
		printf "\n";
	end if;
end for;
printf "\n\nMultiplier ideals that are not in the filtration:\n\n";
for I in multiplierIdealsCopy do
	printf "JN=%-8o ", multiplierIdealToJN[I];
	SNice, extras := MonomialSequence(multiplierIdealToSequence[I], maxContact);
	prt(SNice); for i->elt in extras do printf "g%o = %o\n", i, elt; end for;
end for;

if false then
	// Print filtration
	for i->tup in filtration do
		generators, intersection := Explode(tup);
		printf "KK_i=%-4o ", intersection;
		SNice, extras := MonomialSequence(generators, maxContact);
		prt(SNice); for i->elt in extras do printf "g%o = %o\n", i, elt; end for;
	end for;
	printf "\n";
	// Print multipliers
	for i->tup in multipliers do
		generators, JN := Explode(tup);
		printf "JN=%-8o ", JN;
		SNice, extras := MonomialSequence(generators, maxContact);
		prt(SNice); for i->elt in extras do printf "g%o = %o\n", i, elt; end for;
	end for;
	printf "\n";
end if;




printf "\n\nFinished\n";
quit;

// R<A_43,A_34,A_44,A_52,A_53,A_54> := RationalFunctionField(Q,6);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := y^6 - x^7 + A_52*x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4 + A_53*x^5*y^3 + A_54*x^5*y^4;

// R<t1,t4,t6,t11> := RationalFunctionField(Q,4);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := 1/7*x^7 + 1/5*y^5 -t1*x^3*y^3 -t4*x^5*y^2 -t6*x^4*y^3 -t11*x^5*y^3;

// R<t1,t2,t6,t10> := RationalFunctionField(Q,4);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := -1/9*x^9 -1/4*y^4 +t1*x^7*y +t2*x^5*y^2 +t6*x^6*y^2 +t10*x^7*y^2;

// R<u1,u2,u3,u8,u9,u15> := RationalFunctionField(Q,6);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := x^6 +y^7 +u3*x^4*y^3 +u2*x^3*y^4 +u9*x^4*y^4 +u1*x^2*y^5 +u8*x^3*y^5 +u15*x^4*y^5;

// R<t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17> := RationalFunctionField(Q,18);
// assumeNonzero:={R| t0};
// P<x,y> := LocalPolynomialRing(R,2);
// f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0 + t3*x + t6*x^2 + t9*x^3 + t11*x^4 + t13*x^5 + t7*y + t10*x*y + t12*x^2*y + t14*x^3*y + t15*x^4*y + t16*x^5*y)^2 + (-x^7 + t1*x^5*y + t4*x^6*y + t2*x^3*y^2 + t5*x^4*y^2 + t8*x^5*y^2 + y^3)^2;

//R<t0,t1,t2,t17> := RationalFunctionField(Q,4);
//assumeNonzero:={R| t0};
//P<x,y> := LocalPolynomialRing(R,2);
//f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + t1*x^5*y + y^3)^2;
//f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + t1*x^5*y + t2*x^3*y^2 + y^3)^2;

