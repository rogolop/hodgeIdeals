intrinsic MonomialSequence(S::[], maxContactElements::[]) -> [], []
{   Given a sequence S of polynomials in two variables and a non-empty sequence
    of maximal contact elements (non-constant, irreducible), write each
    polynomial in S as a monomial in terms of the maximal contact elements
    (f1,...,fg,f) and possibly other polynomials (g1,...,gk). Also return
    the sequence of polynomials corresponding to g1,...,gk.
    }
    P<x,y> := Universe(S);
    Q := CoefficientRing(P);
    maxContactElements := [f : f in maxContactElements | (f ne x) and (f ne y)];
    g := #maxContactElements - 1;
    
    factorIndex := AssociativeArray();
    // factorIndex[P!1] := "1";
    variableList := ["x", "y"];
    factorIndex[x] := 1;
    factorIndex[y] := 2;
    maxContactCoeff := [];
    // maxContactElements are f1, f2, ...
    if g gt 0 then
        variableList cat:= ["f" cat IntegerToString(i) : i in [1..g]];
        for i in [1..g] do
            fi := maxContactElements[i];
            factors, coeff := Factorization(fi);
            Append(~maxContactCoeff, coeff);
            fiNormalized := factors[1][1];
            factorIndex[fiNormalized] := 2+i;
        end for;
    end if;
    variableList cat:= ["f"];
    f := maxContactElements[g+1];
    factors, coeff := Factorization(f);
    Append(~maxContactCoeff, coeff);
    fNormalized := factors[1][1];
    factorIndex[fNormalized] := 2+g+1;
    
    // Factorize and store new polynomials
    extraIndex := 0;
    extraPoly := [P| ]; // New polynomials named g1, g2, ...
    // SFactorized := [];
    SFactorized := [car<PowerSequence(car<IntegerRing(),IntegerRing()>),Q>| ];
    for s in S do
        if s in Q then // s is in coefficient ring
            // Append(~SFactorized, <[car<IntegerRing(),IntegerRing()>|], Q!s>);
            Append(~SFactorized, <[], Q!s>);
            continue;
        end if;
        
        factors, coeff := Factorization(s);
        factorsIndexed := [];
        for factor in factors do // h^m
            h := factor[1];
            m := factor[2];
            if not IsDefined(factorIndex, h) then // Define g1, g2, ...
                extraIndex +:= 1;
                name := "g" cat IntegerToString(extraIndex);
                Append(~variableList, name);
                factorIndex[h] := 2+g+1 + extraIndex;
                Append(~extraPoly, h);
            end if;
            Append(~factorsIndexed, <factorIndex[h], m>);
        end for;

        Append(~SFactorized, <factorsIndexed, coeff>);
    end for;
    
    // Write factorizations as monomials in new variables {fi, gi}
    // PExpanded := LocalPolynomialRing(Q, #variableList, "lglex");
    PExpanded := PolynomialRing(Q, #variableList);
    AssignNames(~PExpanded, variableList);
    SExpanded := [PExpanded| ];
    for s in SFactorized do
        factorsIndexed := s[1];
        coeff := s[2];
        
        if #factorsIndexed eq 0 then // s is in coefficient ring
            Append(~SExpanded, coeff);
            continue;
        end if;
        
        term := PExpanded ! coeff;
        for t in factorsIndexed do
            factorIndex := t[1];
            m := t[2];
            
            h := PExpanded.factorIndex;
            if (2+1 le factorIndex) and (factorIndex le 2+g+1) then
                h /:= maxContactCoeff[factorIndex-2];
            end if;
            term *:= h^m;
        end for;
        
        Append(~SExpanded, term);
    end for;
    
    return SExpanded, extraPoly;
end intrinsic;



intrinsic MonomialSequence(I::RngMPol, maxContactElements::[]) -> [], []
{   Given an ideal I of polynomials in two variables and a non-empty sequence
    of maximal contact elements (non-constant, irreducible), write each
    polynomial in the basis of I as a monomial in terms of the maximal contact
    elements (f1,...,fg,f) and possibly other polynomials (g1,...,gk). Also
    return the sequence of polynomials corresponding to g1,...,gk.
    }
    return MonomialSequence(Basis(I), maxContactElements);
end intrinsic;

intrinsic MonomialSequence(I::RngMPolLoc, maxContactElements::[]) -> [], []
{"}
    return MonomialSequence(Basis(I), maxContactElements);
end intrinsic;
