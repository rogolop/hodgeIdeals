AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Attach("MonomialSequence.m");
Attach("ExampleCurve.m");
Z := IntegerRing();
Q := RationalField();

//######################
//### Input/settings
//######################

hideCoinciding := true;
printCoincidingIdeals := false;
printExtraFiltrationIdeals := true;
printMissingMultiplierIdeals := true;
case 2:
	when 1:
		semigroup := [10,15,36]; //[8,12,26,53]; //[6,7]; //[10,15,36];
	when 2:
		// a>=2, b>=a+1, c>=2, d>=1, {a,b,c} pairwise coprime, {c,d} coprime
		abcd := [2,3,5,2]; //[3,8,7,1]; //[4,7,3,1];
end case;

//P<x,y> := LocalPolynomialRing(Q,2); R:=Q;
//f := (y^2-x^3)^5 + x^18; // 10-15-36
//maxContact := [P| x, y, y^2-x^3, f ];
//semigroup := SemiGroup(f);

//######################
//### Everything else
//######################

if not assigned f then
	if assigned abcd then 
		a,b,c,d := Explode(abcd); semigroup := [a*c,b*c,a*b*(c+d)];
	end if;
	f, maxContact := ExampleCurve(semigroup);
	P := Parent(f); x:=P.1; y:=P.2; R := BaseRing(P);
end if;

printf "\nSemigroup %o\n", semigroup;
g := #semigroup -1;
mu := MilnorNumber(f);
printf "mu=%o\n", mu;
printf "f = %o\n", f;
print "maxContact ="; print maxContact;
printf "\n";

prt:=procedure(L)printf"[";for i->l in L do printf"%o%o",&cat Split(Sprintf("%o",l),"*"),i lt#L select", "else"";end for;printf"]";end procedure;

// Calculate

case 1:
	when 1:
		filtration := Filtration(f : N:=mu);
		filtration := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration];
	when 2:
		filtration := [];
		for i in [1..g] do
			filtration_i := FiltrationRupture(f,i : N:=mu);
			filtration_i := [<ChangeUniverse(gen_and_int[1],P), gen_and_int[2]> : gen_and_int in filtration_i];
			for elt in filtration_i do
				if elt notin filtration then Append(~filtration, elt); end if;
			end for;
		end for;
end case;
multipliers := MultiplierIdeals(f);

// Prepare

//print Universe(filtration[1][1]);
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

// Compare filtration vs multipliers

print "Columns:";
print "- Filtration ideal is a multiplier ideal (Y/NO)";
print "- Intersection multiplicity of the clusters?";
print "- Jumping number, or ideal that is not a multiplier ideal";
printf "\n";

multiplierIdealsCopy := multiplierIdeals;
for I in filtrationIdeals do
	if I in multiplierIdealsCopy then
		Exclude(~multiplierIdealsCopy, I);
		if not hideCoinciding then
			printf "   Y %-4o %-8o ", filtrationIdealToInt[I], multiplierIdealToJN[I];
			if printCoincidingIdeals then
				SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
				prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			end if;
			printf "\n";
		end if;
	else
		printf "NO   %-4o ", filtrationIdealToInt[I];
		// printf "        ";
		if printExtraFiltrationIdeals then
			SNice, extras := MonomialSequence(filtrationIdealToSequence[I], maxContact);
			prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			
			printf "\n"; print LogResolution(I);
		end if;
		printf "\n";
	end if;
end for;
printf "\n\nMultiplier ideals that are not in the filtration:\n\n";
if #multiplierIdealsCopy eq 0 then
	printf "None\n";
else
	for I in multiplierIdealsCopy do
		printf "JN=%-8o ", multiplierIdealToJN[I];
		if printMissingMultiplierIdeals then
			SNice, extras := MonomialSequence(multiplierIdealToSequence[I], maxContact);
			prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
			
			printf "\n"; print LogResolution(I);
		end if;
		printf "\n";
	end for;
end if;

printf "\nTotal number of missing multiplier ideals: %o\n", #multiplierIdealsCopy;

// Print all

if false then
	// Print filtration
	for i->tup in filtration do
		generators, intersection := Explode(tup);
		printf "KK_i=%-4o ", intersection;
		SNice, extras := MonomialSequence(generators, maxContact);
		prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
	end for;
	printf "\n";
	printf "\n";
	// Print multipliers
	for i->tup in multipliers do
		generators, JN := Explode(tup);
		printf "JN=%-8o ", JN;
		SNice, extras := MonomialSequence(generators, maxContact);
		prt(SNice); for i->elt in extras do printf "\ng%o = %o", i, elt; end for;
	end for;
	printf "\n";
	printf "\n";
end if;




printf "\n\nFinished\n";
quit;

