intrinsic diagramDataFromProximity(proximityMatrix::Mtrx) -> Tup
	{
		TODO
	}
	Z := Integers();
	numPoints := Ncols(proximityMatrix);
	
	// Calculate dual graph
	N := -Transpose(proximityMatrix) * proximityMatrix;
	M := N; for i in [1..numPoints] do M[i][i] := 0; end for;
	children := [];
	parent := [Z| ];
	visited := {Z| }; pending := {Z| 1}; // temp
	while #visited lt numPoints do
		pt := Representative(pending);
		Exclude(~pending, pt);
		Include(~visited, pt);
		children[pt] := [Z| i : i in [1..numPoints] | M[pt][i] eq 1 and i notin visited];
		for child in children[pt] do
			Include(~pending, child);
			parent[child] := pt;
		end for;
	end while;
	mainRow := [Z| numPoints];
	while mainRow[#mainRow] ne 1 do
		Append(~mainRow, parent[mainRow[#mainRow]]);
	end while;
	Reverse(~mainRow);
	dualGraphBranches := [[Z| ] : i in [1..numPoints]];
	for pt in mainRow do
		nonMainNeighbors := [Z| child : child in children[pt] | child notin mainRow];
		if #nonMainNeighbors gt 0 then
			pt2 := nonMainNeighbors[1];
			dualGraphBranches[pt] := [Z| pt2];
			while #children[pt2] gt 0 do
				pt2 := children[pt2][1];
				Append(~dualGraphBranches[pt], pt2);
			end while;
		end if;
	end for;
	dualGraphMatrix := ZeroMatrix(Z, 1+Max([#seq : seq in dualGraphBranches]), #mainRow);
	for i->pt in mainRow do
		dualGraphMatrix[1][i] := pt;
		for j->pt2 in dualGraphBranches[pt] do
			dualGraphMatrix[1+j][i] := pt2;
		end for;
	end for;
	
	// Calculate Enriques diagram
	isFree := [ &+Eltseq(proximityMatrix[pt]) ge 0 : pt in [1..numPoints]];
	enriques := ZeroMatrix(Z, 2*numPoints);
	i:=1; j:=1; di:=0; dj:=1;
	lastProximateTo := 0;
	enriques[1][1] := 1;
	lastWasSatellite := false;
	for pt in [2..numPoints] do
		if isFree[pt] then
			if lastWasSatellite then
				j +:= 1;
				enriques[i][j] := -1;
				while i gt 1 do
					i -:= 1;
					enriques[i][j] := -2;
				end while;
				enriques[i][j] := -3;
			end if;
			lastWasSatellite := false;
			i:=1; di:=0; dj:=1;
		else
			proximateTo := Min([Z| k : k in [1..numPoints] | proximityMatrix[pt][k] eq -1]);
			if lastProximateTo ne proximateTo then
				di, dj := Explode(<dj,di>);
			end if;
			lastProximateTo := proximateTo;
			lastWasSatellite := true;
		end if;
		i +:= di; j +:= dj;
		enriques[i][j] := pt;
	end for;
	actualHeight := Max([Z| k : k in [1..Nrows(enriques)] | &+Eltseq(enriques[k]) ne 0]);
	actualWidth := Max([Z| k : k in [1..Ncols(enriques)] | &+Eltseq(Transpose(enriques)[k]) ne 0]);
	enriques := Submatrix(enriques, 1,1, actualHeight, actualWidth);
	
	return <dualGraphMatrix, enriques>;
end intrinsic;

intrinsic printAnnotatedDualGraph(diagramData::Tup, annotations::Any : vertSep:="│", horizSep:="───")
	{
		TODO
	}
	dualGraphMatrix, enriques := Explode(diagramData);
	Z := Integers();
	for j in [1..Ncols(dualGraphMatrix)] do
		if j gt 1 then printf vertSep; else
			if vertSep eq "│" then printf "╷"; end if;
		end if;
		for i in [1..Nrows(dualGraphMatrix)] do
			pt := dualGraphMatrix[i][j];
			if pt eq 0 then break; end if;
			if i gt 1 then printf horizSep; end if;
			printf "%o", annotations[pt];
		end for;
		printf "\n";
	end for;
end intrinsic;

intrinsic printAnnotatedEnriquesDiagram(diagramData::Tup, annotations::Any)
	{
		TODO
	}
	dualGraphMatrix, enriques := Explode(diagramData);
	Z := Integers();
	maxLabelSize := Max([Z| #Sprintf("%o",ann) : ann in Eltseq(annotations)]);
	for i in [1..Nrows(enriques)] do
	for j in [1..Ncols(enriques)] do
		case enriques[i][j]:
		when 0:
			printf " " cat " "^maxLabelSize;
		when -1:
			printf "─"^Ceiling((maxLabelSize)/ 2) cat "╯" cat
				" "^Floor((maxLabelSize)/ 2);
		when -2:
			printf " "^Ceiling((maxLabelSize)/ 2) cat "│" cat
				" "^Floor((maxLabelSize)/ 2);
		when -3:
			printf " "^Ceiling((maxLabelSize)/ 2) cat "╭" cat
				"─"^Floor((maxLabelSize)/ 2);
		else:
			ann := Sprintf("%o",annotations[enriques[i][j]]);
			prefix := " ";
			if j gt 1 then
				if i eq 1 then
					prefix := "~";
				else
					if enriques[i][j-1] gt 0 then
						prefix := "─";
					end if;
				end if;
			end if;
			printf "%o%o", &cat[prefix:k in [1..1+maxLabelSize-#ann]], ann;
		end case;
	end for;
	printf "\n";
	end for;
end intrinsic;

intrinsic printAnnotatedEnriquesDiagramAndDualGraph(diagramData::Tup, annotations::Any : vertSep:="│", horizSep:="───", sideBySide:=true)
	{
		TODO
	}
	if sideBySide then
		dualGraphMatrix, enriques := Explode(diagramData);
		Z := Integers();
		maxLabelSize := Max([Z| #Sprintf("%o",ann) : ann in Eltseq(annotations)]);
		for i in [1..Max(Nrows(enriques), Ncols(dualGraphMatrix))] do
			if i le Nrows(enriques) then
				for j in [1..Ncols(enriques)] do
					case enriques[i][j]:
					when 0:
						printf " " cat " "^maxLabelSize;
					when -1:
						printf "─"^Ceiling((maxLabelSize)/ 2) cat "╯" cat
							" "^Floor((maxLabelSize)/ 2);
					when -2:
						printf " "^Ceiling((maxLabelSize)/ 2) cat "│" cat
							" "^Floor((maxLabelSize)/ 2);
					when -3:
						printf " "^Ceiling((maxLabelSize)/ 2) cat "╭" cat
							"─"^Floor((maxLabelSize)/ 2);
					else:
						ann := Sprintf("%o",annotations[enriques[i][j]]);
						prefix := " ";
						if j gt 1 then
							if i eq 1 then
								prefix := "~";
							else
								if enriques[i][j-1] gt 0 then
									prefix := "─";
								end if;
							end if;
						end if;
						printf "%o%o", &cat[prefix:k in [1..1+maxLabelSize-#ann]], ann;
					end case;
				end for;
			else
				for j in [1..Ncols(enriques)] do
					printf " " cat " "^maxLabelSize;
				end for;
			end if;
			printf "    ";
			
			if i le Ncols(dualGraphMatrix) then
				if i gt 1 then printf vertSep; else
					if vertSep eq "│" then printf "╷"; end if;
				end if;
				for j in [1..Nrows(dualGraphMatrix)] do
					pt := dualGraphMatrix[j][i];
					if pt eq 0 then break; end if;
					if j gt 1 then printf horizSep; end if;
					printf "%o", annotations[pt];
				end for;
			end if;
		
			printf "\n";
		end for;
	else
		printAnnotatedEnriquesDiagram(diagramData, annotations);
		printAnnotatedDualGraph(diagramData, annotations);
	end if;
end intrinsic;



