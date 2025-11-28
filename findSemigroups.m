// Find semigroups with coincidences between the jumping numbers of 3 rupture divisors

AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Attach("MonomialSequence.m");
Attach("ExampleCurve.m");
Attach("planeCurveDiagrams.m");
import "SingularitiesDim2/IntegralClosure.m": Unloading;
Z := IntegerRing();
Q := RationalField();


// n1,n2,n3>=2, n1>a, n2>b, n3>c
//  pairwise coprime: {n1,n2,n3,a}, {n2,n3,b}, {n3,c}

semigroups := [];
n1Range := [2..15];
n2Range := [2..15];
n3Range := [2..15];
aMax := 15;
bMax := 15;
cMax := 15;
for i->n1 in n1Range do
for j->n2 in n2Range do
if GCD(n1,n2) ne 1 then continue; end if;
for k->n3 in n3Range do
if GCD(n1,n3) ne 1 or GCD(n2,n3) ne 1 then continue; end if;
	printf "Approx. progress: %o/%o\n", (k-2) + (j-2) * #n3Range + i * #n3Range * #n2Range, #n3Range * #n2Range * #n1Range;
	for a in [n1+1..aMax] do
	if GCD(n1,a) ne 1 or GCD(n2,a) ne 1 or GCD(n3,a) ne 1 then continue; end if;
	for b in [n2+1..bMax] do
	if GCD(n2,b) ne 1 or GCD(n3,b) ne 1 then continue; end if;
	for c in [n3+1..cMax] do
	if GCD(n3,c) ne 1 then continue; end if;
	
	G := [n1*n2*n3, n2*n3*a, n1*n3*a*b, n1*n2*a*b*c];
	mu := MilnorNumber(G);
	Append(~semigroups, <mu,[n1,n2,n3,a,b,c],G>);
	
	end for;
	end for;
	end for;
end for;
end for;
end for;
// semigroups := [tup : tup in semigroups | MilnorNumber(tup[2]) le 420];
printf "Semigroups calculated\n";
// printf "Milnor numbers calculated\n";
// ParallelSort(~milnorNumbers, ~semigroups);
Sort(~semigroups);
printf "Sorted\n\n";
print semigroups;




printf "\n\nFinished\n";
quit;

