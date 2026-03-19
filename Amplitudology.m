(* ::Package:: *)

(* ::Title:: *)
(*Amplitudology*)


(* ::Subtitle:: *)
(*Package to perform symbolic and numerical amplitude computations*)


Quit[]


(* ::Chapter::Closed:: *)
(*Symbolic*)


(* ::Section::Closed:: *)
(*Symbolic Expressions*)


(* ::Text:: *)
(*Define abstract spinors and vectors and polarisation vectors, and set attributes of various functions*)


SetAttributes[spA,Protected];
SetAttributes[spS,Protected];
SetAttributes[vec,Protected];
SetAttributes[m,Protected];
SetAttributes[pol,Protected];
SetAttributes[polb,Protected];
SetAttributes[Ubar,Protected];
SetAttributes[V,Protected];
SetAttributes[agp,Protected];
SetAttributes[dpID,Protected];


(* ::Text:: *)
(*Define dimension variable (defaults to 4D)*)


$dim = 4;


(*covariant Heads*)(*write covariant objects such that the functions below can recognise them*)
covheads = {vec,pol,polb,Svec,spS,spA};


(* ::Text:: *)
(*Define properties of spinor and vector products*)


(*ANGLE PROD*)
ClearAll[ap];
(*linearity*)
ap[\[Lambda]1_ a1_spA,rest__] := \[Lambda]1 ap[a1,rest];
ap[rest__,\[Lambda]1_ a1_spA] := - \[Lambda]1 ap[a1,rest];
ap[left__,right__] /; Head[left]===Plus || Head[right]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(ap[#[[1]],#[[2]]]&/@Flatten[Outer[List,list@left,list@right],1])
	];
(*antisymmetry*)
ap[a_spA,a_spA] := 0;
ap[a2_spA,a1_spA] /; !SameQ[a1,a2] && OrderedQ[{a1,a2}] := - ap[a1,a2];


(*SQUARE PROD*)
ClearAll[sp];
(*linearity*)
sp[\[Lambda]1_ s1_spS,rest__] := \[Lambda]1 sp[s1,rest];
sp[rest__,\[Lambda]1_ s1_spS] := - \[Lambda]1 sp[s1,rest];
sp[left__,right__] /; Head[left]===Plus || Head[right]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(sp[#[[1]],#[[2]]]&/@Flatten[Outer[List,list@left,list@right],1])
	];
(*antisymmetry*)
sp[s_spS,s_spS] := 0;
sp[s2_spS,s1_spS] /; !SameQ[s1,s2] && OrderedQ[{s1,s2}] := - sp[s1,s2];


(*SPINOR MOM PROD*)
(* -----  OLD VERSION -----
ClearAll[momp];
(*linearity*)
momp[\[Lambda]_ s_spS,p__,a__] := \[Lambda] momp[s,p,a];
momp[s__,\[Lambda]_ p_vec,a__] := \[Lambda] momp[s,p,a];
momp[s__,p__,\[Lambda]_ a_spA] := \[Lambda] momp[s,p,a];
momp[s__,p__,a__] /; Head[s]===Plus || Head[p]===Plus || Head[a]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(momp[#[[1]],#[[2]],#[[3]]]&/@Flatten[Outer[List,list@s,list@p,list@a],2])
	];
(*Dirac equation*)
momp[s_spS,vec[x_],spA[x_]] := m[x] sp[s,spS[x]];
momp[spS[x_],vec[x_],a_spA] := - m[x] ap[spA[x],a];
----- END OLD VERSION ----- *)


(*DIRAC SPINORS & SPINOR PROD*)
ClearAll[momp,mompSimplify,mompAutoSimplify];
(*reduction to sp and ap*)
momp[s1_spS,s2_spS] := sp[s1,s2];
momp[s1_spA,s2_spA] := ap[s1,s2];
(*linearity*)
momp[s_,left___,p_Plus,right___,a_] := momp[s,left,#,right,a]&/@p;
momp[s_Plus,left___,p_,right___,a_] := momp[#,left,p,right,a]&/@s;
momp[s_,left___,p_,right___,a_Plus] := momp[s,left,p,right,#]&/@a;
momp[s_,left___,\[Lambda]_ p_,right___,a_] /; MemberQ[covheads,Head[p]] := \[Lambda] momp[s,left,p,right,a];
momp[s_,left___,p_,right___,\[Lambda]_ a_] /; MemberQ[covheads,Head[a]] := \[Lambda] momp[s,left,p,right,a];
momp[\[Lambda]_ s_,left___,p_,right___,a_] /; MemberQ[covheads,Head[s]] := \[Lambda] momp[s,left,p,right,a];
(*Dirac*)
momp[spS[i_],vec[i_],rest___,a_] /; MemberQ[OSM,i] := -m[i] momp[spA[i],rest,a];
momp[spA[i_],vec[i_],rest___,a_] /; MemberQ[OSM,i] := -m[i] momp[spS[i],rest,a];
momp[s_,rest___,vec[j_],spS[j_]] /; MemberQ[OSM,j] := m[j]momp[s,rest,spA[j]];
momp[s_,rest___,vec[j_],spA[j_]] /; MemberQ[OSM,j] := m[j]momp[s,rest,spS[j]];
(*zero*)
momp[left___,0,right___]:=0;
(*remove double terms*)
momp[s_,left___,var_,var_,right___,a_] := dot[var,var] momp[s,left,right,a];
(*useful rearrangements*)(*NB these will be followed IN ORDER!!*)
(*NB THE BELOW CODE IS TIME-CONSUMING, SO DEFINE A FUNCTION TO USE IT AT WILL, AND A VARIABLE TO USE IT AUTOMATICALLY*)
(*activation variable*)
mompAutoSimplify = True;
(*first rearrange to remove double terms*)(*use 'double' head to only do one pair at a time, and avoid conflict with more than one repeated elems*)
dot[double[var_],double[var_]] /; mompAutoSimplify := dot[var,var];
momp[s_,left___,double[var_],neigh_,middle___,double[var_],right___,a_]/; mompAutoSimplify := 2dot[var,neigh]momp[s,left,middle,var,right,a]-momp[s,left,neigh,double[var],middle,double[var],right,a];
momp[s_,left___,var_,neigh_,middle___,var_,right___,a_]/; mompAutoSimplify := 2dot[var,neigh]momp[s,left,middle,var,right,a]-momp[s,left,neigh,double[var],middle,double[var],right,a];
(*then rearrange to use Dirac*)
momp[spS[i_],left___,neigh_,vec[i_],right___,a_] /; mompAutoSimplify&&MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] := 2dot[neigh,vec[i]]momp[spS[i],left,right,a]-momp[spS[i],left,vec[i],neigh,right,a];
momp[spA[i_],left___,neigh_,vec[i_],right___,a_] /; mompAutoSimplify&&MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] := 2dot[neigh,vec[i]]momp[spA[i],left,right,a]-momp[spA[i],left,vec[i],neigh,right,a];
momp[s_,left___,vec[j_],neigh_,right___,spS[j_]] /; mompAutoSimplify&&MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] := 2dot[neigh,vec[j]]momp[s,left,right,spS[j]]-momp[s,left,neigh,vec[j],right,spS[j]];
momp[s_,left___,vec[j_],neigh_,right___,spA[j_]] /; mompAutoSimplify&&MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] := 2dot[neigh,vec[j]]momp[s,left,right,spA[j]]-momp[s,left,neigh,vec[j],right,spA[j]];
(*once all the above is done, rearrange the terms in canonical order*)
momp[s_,left___,var2_,var1_,right___,a_] /; mompAutoSimplify&&!OrderedQ[{var2,var1}] := 2dot[var1,var2]momp[s,left,right,a] - momp[s,left,var1,var2,right,a];
(*use the above as replacement rules*)
mompSimplify[expr___] := expr//.{
dot[double[var_],double[var_]] :> dot[var,var],
momp[s_,left___,double[var_],neigh_,middle___,double[var_],right___,a_] :> 2dot[var,neigh]momp[s,left,middle,var,right,a]-momp[s,left,neigh,double[var],middle,double[var],right,a],
momp[s_,left___,var_,neigh_,middle___,var_,right___,a_] :> 2dot[var,neigh]momp[s,left,middle,var,right,a]-momp[s,left,neigh,double[var],middle,double[var],right,a],
momp[spS[i_],left___,neigh_,vec[i_],right___,a_] /; MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] :> 2dot[neigh,vec[i]]momp[spS[i],left,right,a]-momp[spS[i],left,vec[i],neigh,right,a];
momp[spA[i_],left___,neigh_,vec[i_],right___,a_] /; MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] :> 2dot[neigh,vec[i]]momp[spA[i],left,right,a]-momp[spA[i],left,vec[i],neigh,right,a];
momp[s_,left___,vec[j_],neigh_,right___,spS[j_]] /; MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] :> 2dot[neigh,vec[j]]momp[s,left,right,spS[j]]-momp[s,left,neigh,vec[j],right,spS[j]];
momp[s_,left___,vec[j_],neigh_,right___,spA[j_]] /; MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] :> 2dot[neigh,vec[j]]momp[s,left,right,spA[j]]-momp[s,left,neigh,vec[j],right,spA[j]];
momp[s_,left___,var2_,var1_,right___,a_] /; !OrderedQ[{var2,var1}] :> 2dot[var1,var2]momp[s,left,right,a] - momp[s,left,var1,var2,right,a]
};


(*chiral traces*)
ClearAll[trP,trM];
chiralTrAutoSimplify = False;
momp[spS[k1_],vec[p1_],spA[k2_]]momp[spS[k2_],vec[p2_],spA[k1_]] /; chiralTrAutoSimplify ^:= trP[vec[k1],vec[p1],vec[k2],vec[p2]];
chiralTr = {
trP[i1_,i2_,i3_,i4_] :> 2dot[i1,i2]dot[i3,i4]+2dot[i1,i4]dot[i3,i2]-2dot[i1,i3]dot[i2,i4]+2I epsilon[i1,i2,i3,i4],
trM[i1_,i2_,i3_,i4_] :> 2dot[i1,i2]dot[i3,i4]+2dot[i1,i4]dot[i3,i2]-2dot[i1,i3]dot[i2,i4]-2I epsilon[i1,i2,i3,i4]
};


(*LEVI-CIVITA (any number of indices*)
ClearAll[epsilon];
(*zero*)
epsilon[left___,0,right___]:=0;
(*linearity*)
epsilon[left___,\[Lambda]_ a_,right___] /; MemberQ[covheads,Head@a] := \[Lambda] epsilon[left,a,right];
epsilon[left___,p_Plus,right___] := epsilon[left,#,right]&/@p;
(*full antisymmetry*)(*any variable*)
epsilon[seq__] /; !DuplicateFreeQ[{seq}] := 0;
epsilon[seq__] /; DuplicateFreeQ[{seq}] && !OrderedQ[{seq}] := Signature[{seq}] epsilon[Sequence@@Sort[{seq}]];
(*square*)
removeEpsSq = {
epsilon[seq1__]epsilon[seq2__] :> - Plus@@((Signature[#]Times@@Thread@dot[{seq1},#])&/@Permutations[{seq2}]),
epsilon[seq1__]^n_ :> epsilon[seq1]^(n-2) (- Plus@@((Signature[#]Times@@Thread@dot[{seq1},#])&/@Permutations[{seq1}]))
};


(*DOT PROD*)
ClearAll[dot];
(*zero*)
dot[left___,0,right___]:=0;
(* p^2 *)
SimplifyPSquare = False;
dot[vec[x_],vec[y_]] /; SameQ[x,y]&&SimplifyPSquare := m[x]^2;
dot[vec[x_],vec[x_]] /; !SimplifyPSquare&&MemberQ[OSM,x] := m[x]^2;
(* P \[Epsilon] *)
dot[pol[x_],vec[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*NB: now (21/09/2021) this is ONLY imposed on ONSHELL legs. This may cause issues in older code*)
dot[polb[x_],vec[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;
dot[pol[x_],pol[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*added 14/12/2021, de-activate if needed*)
dot[polb[x_],polb[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*added 14/12/2021, de-activate if needed*)
(*dot[pol[x_],polb[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 1;*)(*added 14/12/2021, de-activate if needed*)
(*ordering*)
(*dot[vec[y_],vec[x_]] /; !SameQ[x,y] && OrderedQ[{x,y}] := dot[vec[x],vec[y]];
dot[vec[y_],pol[x_]] := dot[pol[x],vec[y]];
dot[pol[y_],pol[x_]] /; !SameQ[x,y] && OrderedQ[{x,y}] := dot[pol[x],pol[y]];*)
SetAttributes[dot,Orderless];(*NB: new (5/11/2021). Older code above*)
(*linearity*)
dot[\[Lambda]_ v_,a__] /;MemberQ[covheads,Head[v]]:= \[Lambda] dot[v,a];
dot[a__,\[Lambda]_ v_] /;MemberQ[covheads,Head[v]]:= \[Lambda] dot[a,v];
dot[a__,b__] /; Head[a]===Plus || Head[b]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(dot[#[[1]],#[[2]]]&/@Flatten[Outer[List,list@a,list@b],1])
	];
(*square*)
dot[x_] := dot[x,x];
(*FIELD STRENGTHS*)
ClearAll[F];
F[a_][l___,0,r___] := 0;
F[a_][x_,x_] := 0;
F[a_][x_,y_] /; !OrderedQ[{x,y}] := -F[a][y,x];
(*linearity*)
F[x_][\[Lambda]_ v_,a__] /;MemberQ[covheads,Head[v]]:= \[Lambda] F[x][v,a];
F[x_][a__,\[Lambda]_ v_] /;MemberQ[covheads,Head[v]]:= \[Lambda] F[x][a,v];
F[x_][a__,b__] /; Head[a]===Plus || Head[b]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(F[x][#[[1]],#[[2]]]&/@Flatten[Outer[List,list@a,list@b],1])
	];
(*contractions*)
ClearAll[ttFF,tFF];
tFF[a_,b_][l___,0,r___] := 0;
ttFF[a_,b_]/;!OrderedQ[{a,b}]:=ttFF[b,a];
tFF[a_,b_][l_,r_]/;!OrderedQ[{a,b}]:=tFF[b,a][r,l];
tFF[a_,b_][left___,\[Lambda]_ v_,right___] /;MemberQ[covheads,Head[v]]:= \[Lambda] tFF[a,b][left,v,right];
tFF[a_,b_][x__,y__] /; Head[x]===Plus || Head[y]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(tFF[a,b][#[[1]],#[[2]]]&/@Flatten[Outer[List,list@x,list@y],1])
	];
(*AUTO-CONTRACTING LORENTZ INDICES*)
ClearAll[ind];
(*dot product contraction*)
dot[l1___,ind[x_],r1___]dot[l2___,ind[x_],r2___] ^:= dot[Sequence[l1,r1],Sequence[l2,r2]];
dot/:dot[l1___,ind[x_],r1___]^2 := dot[Sequence[l1,r1],Sequence[l1,r1]];
dot[ind[x_],ind[x_]] := $dim;
(*Levi-Civita*)
epsilon/:epsilon[a___,in_,z___]dot[l___,in_,r___]/; Head[in]===ind := epsilon[a,l,r,z];
(*field strenghts*)
F[a_][ind[x_],ind[y_]]dot[ind[x_],ind[y_]] ^:= F[a][ind[x],ind[x]];
F[a_][ind[x_],ind[y_]]dot[l1___,ind[x_],r1___]dot[l2___,ind[y_],r2___] ^:= F[a][l1,r1,l2,r2];
F[a_][left___,ind[x_],right___]dot[l___,ind[x_],r___] ^:= F[a][left,l,r,right];
(*F[a_][ind[x_],ind[y_]]F[b_][ind[x_],ind[y_]] ^:= ttFF[a,b];
F[a_][la___,ind[x_],ra___]F[b_][lb___,ind[x_],rb___] ^:= (-1)^(Length[{1,ra}]+Length[{1,lb}]) tFF[a,b][la,ra,lb,rb];
(*contracted field strengths*)
SetAttributes[ttFF,Orderless];
tFF[a_,b_][l_,r_]/;!OrderedQ[{a,b}]:=tFF[b,a][r,l];*)


(*DOT PROD: alternative, e.g. to use for restriction to a subspace*)
ClearAll[odot];
(*zero*)
odot[left___,0,right___]:=0;
(* p^2 *)
SimplifyPSquare = False;
odot[vec[x_],vec[y_]] /; SameQ[x,y]&&SimplifyPSquare := m[x]^2;
odot[vec[x_],vec[x_]] /; !SimplifyPSquare&&MemberQ[OSM,x] := m[x]^2;
(* P \[Epsilon] *)
odot[pol[x_],vec[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*NB: now (21/09/2021) this is ONLY imposed on ONSHELL legs. This may cause issues in older code*)
odot[polb[x_],vec[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;
odot[pol[x_],pol[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*added 14/12/2021, de-activate if needed*)
odot[polb[x_],polb[y_]] /; SameQ[x,y] && MemberQ[OSM,x] := 0;(*added 14/12/2021, de-activate if needed*)
SetAttributes[odot,Orderless];(*NB: new (5/11/2021). Older code above*)
(*linearity*)
odot[\[Lambda]_ v_,a__] /;MemberQ[covheads,Head[v]]:= \[Lambda] odot[v,a];
odot[a__,\[Lambda]_ v_] /;MemberQ[covheads,Head[v]]:= \[Lambda] odot[a,v];
odot[a__,b__] /; Head[a]===Plus || Head[b]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(odot[#[[1]],#[[2]]]&/@Flatten[Outer[List,list@a,list@b],1])
	];
(*square*)
odot[x_] := odot[x,x];


(*rule to expand F*)
ClearAll[Frule,Frule0];
Frule0 = F[l_][x_,y_]:>dot[x,vec[l]]dot[y,pol[l]]-dot[y,vec[l]]dot[x,pol[l]];
Frule = {
(*F[ref[l_]][x_,y_]:>dot[x,vec[l]]dot[y,pol[ref[l]]]-dot[y,vec[l]]dot[x,pol[ref[l]]],*)
F[l_][x_,y_]:>dot[x,vec[l]]dot[y,pol[l]]-dot[y,vec[l]]dot[x,pol[l]],
tFF[i_,j_][x_,y_]:>-dot[x,vec[i]] dot[y,vec[j]] dot[pol[i],pol[j]]+dot[x,vec[i]] dot[y,pol[j]] dot[pol[i],vec[j]]+dot[x,pol[i]] dot[y,vec[j]] dot[pol[j],vec[i]]-dot[x,pol[i]] dot[y,pol[j]] dot[vec[i],vec[j]],
ttFF[i_,j_]:>-2 dot[pol[i],vec[j]] dot[pol[j],vec[i]]+2 dot[pol[i],pol[j]] dot[vec[i],vec[j]]
};


(*DIRAC SPINORS & SPINOR PROD*)
ClearAll[dp,dpSimplify,dpAutoSimplify];
(*make list of on-shell momenta*)(*needed by dot and dp*)
dponshell[list_] := OSM=list;
(*properties of Gamma5 matrix, to be used below*)
dot[Gamma5,Gamma5]:=1;
dot[Gamma5,var_]:=0;
dot[var_,Gamma5]:=0;
(*identity element*)
dp[ub_Ubar,left___,coeff_ dpID,right___,v_V] := coeff dp[ub,left,right,v];
(*linearity*)
dp[u_Ubar,left___,p_Plus,right___,v_V] := dp[u,left,#,right,v]&/@p;
dp[u_Ubar,left___,\[Lambda]_ p_,right___,v_V] /; Head[p]===vec || Head[p]===pol || Head[p]===agp := \[Lambda] dp[u,left,p,right,v];
(*antisymmetric gamma products*)
dp[ub_Ubar,left___,agp[vars___],right___,v_V] := Signature@List@vars/(Length@List[vars])! Plus@@Times@@@({dp[ub,left,Sequence@@#,right,v]&@#[[1]],#[[2]]}&/@({#,Signature@#}&/@Permutations[List[vars]]));
(*Dirac*)
dp[Ubar[i_],vec[i_],rest___,v_V] /; MemberQ[OSM,i] := m[i] dp[Ubar[i],rest,v];
dp[ub_Ubar,rest___,vec[j_],V[j_]] /; MemberQ[OSM,j] := -m[j]dp[ub,rest,V[j]];
(*gamma-traces (ONLY for on-shell polarisations)*)
dp[Ubar[i_],pol[i_],rest___,v_V] /; MemberQ[OSM,i] := 0;
dp[ub_Ubar,rest___,pol[j_],V[j_]] /; MemberQ[OSM,j] := 0;
(*remove double terms*)
dp[ub_Ubar,left___,var_,var_,right___,v_V] := dot[var,var] dp[ub,left,right,v];
(*useful rearrangements*)(*NB these will be followed IN ORDER!!*)
(*NB THE BELOW CODE IS TIME-CONSUMING, SO DEFINE A FUNCTION TO USE IT AT WILL, AND A VARIABLE TO USE IT AUTOMATICALLY*)
(*activation variable*)
dpAutoSimplify = False;
(*first rearrange to remove double terms*)(*use 'double' head to only do one pair at a time, and avoid conflict with more than one repeated elems*)
dot[double[var_],double[var_]] /; dpAutoSimplify := dot[var,var];
dp[ub_Ubar,left___,double[var_],neigh_,middle___,double[var_],right___,v_V]/; dpAutoSimplify := 2dot[var,neigh]dp[ub,left,middle,var,right,v]-dp[ub,left,neigh,double[var],middle,double[var],right,v];
dp[ub_Ubar,left___,var_,neigh_,middle___,var_,right___,v_V]/; dpAutoSimplify := 2dot[var,neigh]dp[ub,left,middle,var,right,v]-dp[ub,left,neigh,double[var],middle,double[var],right,v];
(*then rearrange to use Dirac*)
dp[Ubar[i_],left___,neigh_,vec[i_],right___,v_V] /; dpAutoSimplify&&MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] := 2dot[neigh,vec[i]]dp[Ubar[i],left,right,v]-dp[Ubar[i],left,vec[i],neigh,right,v];
dp[ub_Ubar,left___,vec[j_],neigh_,right___,V[j_]] /; dpAutoSimplify&&MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] := 2dot[neigh,vec[j]]dp[ub,left,right,V[j]]-dp[ub,left,neigh,vec[j],right,V[j]];
(*then rearrange to use gamma-traces*)
dp[Ubar[i_],left___,neigh_,pol[i_],right___,v_V] /; dpAutoSimplify&&MemberQ[OSM,i]&&!SameQ[neigh,pol[i]] := 2dot[neigh,pol[i]]dp[Ubar[i],left,right,v]-dp[Ubar[i],left,pol[i],neigh,right,v];
dp[ub_Ubar,left___,pol[j_],neigh_,right___,V[j_]] /; dpAutoSimplify&&MemberQ[OSM,j]&&!SameQ[neigh,pol[j]] := 2dot[neigh,pol[j]]dp[ub,left,right,V[j]]-dp[ub,left,neigh,pol[j],right,V[j]];
(*once all the above is done, rearrange the terms in canonical order*)
dp[ub_Ubar,left___,var2_,var1_,right___,v_V] /; dpAutoSimplify&&!OrderedQ[{var2,var1}] := 2dot[var1,var2]dp[ub,left,right,v] - dp[ub,left,var1,var2,right,v];
(*use the above as replacement rules*)
dpSimplify[expr___] := expr//.{
dot[double[var_],double[var_]] :> dot[var,var],
dp[ub_Ubar,left___,double[var_],neigh_,middle___,double[var_],right___,v_V] :> 2dot[var,neigh]dp[ub,left,middle,var,right,v]-dp[ub,left,neigh,double[var],middle,double[var],right,v],
dp[ub_Ubar,left___,var_,neigh_,middle___,var_,right___,v_V] :> 2dot[var,neigh]dp[ub,left,middle,var,right,v]-dp[ub,left,neigh,double[var],middle,double[var],right,v],
dp[Ubar[i_],left___,neigh_,vec[i_],right___,v_V] /; MemberQ[OSM,i]&&!SameQ[neigh,vec[i]] :> 2dot[neigh,vec[i]]dp[Ubar[i],left,right,v]-dp[Ubar[i],left,vec[i],neigh,right,v],
dp[ub_Ubar,left___,vec[j_],neigh_,right___,V[j_]] /; MemberQ[OSM,j]&&!SameQ[neigh,vec[j]] :> 2dot[neigh,vec[j]]dp[ub,left,right,V[j]]-dp[ub,left,neigh,vec[j],right,V[j]],
dp[Ubar[i_],left___,neigh_,pol[i_],right___,v_V] /; MemberQ[OSM,i]&&!SameQ[neigh,pol[i]] :> 2dot[neigh,pol[i]]dp[Ubar[i],left,right,v]-dp[Ubar[i],left,pol[i],neigh,right,v],
dp[ub_Ubar,left___,pol[j_],neigh_,right___,V[j_]] /; MemberQ[OSM,j]&&!SameQ[neigh,pol[j]] :> 2dot[neigh,pol[j]]dp[ub,left,right,V[j]]-dp[ub,left,neigh,pol[j],right,V[j]],
dp[ub_Ubar,left___,var2_,var1_,right___,v_V] /; !OrderedQ[{var2,var1}] :> 2dot[var1,var2]dp[ub,left,right,v] - dp[ub,left,var1,var2,right,v]
};


(*(*LEVI-CIVITA (just 4 indices)*)
ClearAll[epsilon];
(*zero*)
epsilon[left___,0,right___]:=0;
(*linearity*)
epsilon[\[Lambda]_ a_,b__,c__,d__] /; MemberQ[covheads,Head@a] := \[Lambda] epsilon[a,b,c,d];
epsilon[a__,\[Lambda]_ b_,c__,d__] /; MemberQ[covheads,Head@b] := \[Lambda] epsilon[a,b,c,d];
epsilon[a__,b__,\[Lambda]_ c_,d__] /; MemberQ[covheads,Head@c] := \[Lambda] epsilon[a,b,c,d];
epsilon[a__,b__,c__,\[Lambda]_ d_] /; MemberQ[covheads,Head@d] := \[Lambda] epsilon[a,b,c,d];
epsilon[a__,b__,c__,d__] /; Head[a]===Plus || Head[b]===Plus || Head[c]===Plus || Head[d]===Plus := 
	With[{list = If[Head[#] === Plus,List@@#,{#}]&},
		Plus@@(epsilon[#[[1]],#[[2]],#[[3]],#[[4]]]&/@Flatten[Outer[List,list@a,list@b,list@c,list@d],3])
	];
(*full antisymmetry*)(*pol-vec only*)
(*epsilon[a_,b_,c_,d_] /; (Head/@{a,b,c,d}/.{vec->Nothing,pol->Nothing})==={} && !DuplicateFreeQ[{a,b,c,d}] := 0;
epsilon[a_,b_,c_,d_] /; (Head/@{a,b,c,d}/.{vec->Nothing,pol->Nothing})==={} && DuplicateFreeQ[{a,b,c,d}] && !OrderedQ[{a,b,c,d}] := Signature[{a,b,c,d}] epsilon[Sequence@@Sort[{a,b,c,d}]];*)
(*full antisymmetry*)(*any variable*)
epsilon[a_,b_,c_,d_] /; !DuplicateFreeQ[{a,b,c,d}] := 0;
epsilon[a_,b_,c_,d_] /; DuplicateFreeQ[{a,b,c,d}] && !OrderedQ[{a,b,c,d}] := Signature[{a,b,c,d}] epsilon[Sequence@@Sort[{a,b,c,d}]];
(*square*)
removeEpsSq = {
epsilon[a_,b_,c_,d_]epsilon[e_,f_,g_,h_] (*/; (Head/@{a,b,c,d}/.{vec->Nothing,pol->Nothing})==={} && (Head/@{e,f,g,h}/.{vec->Nothing,pol->Nothing})==={} && OrderedQ[{a,b,c,d}] && OrderedQ[{e,f,g,h}]*) :> - Plus@@((Signature[#]dot[a,#[[1]]]dot[b,#[[2]]]dot[c,#[[3]]]dot[d,#[[4]]])&/@Permutations[{e,f,g,h}]),
epsilon[a_,b_,c_,d_]^n_ (*/; (Head/@{a,b,c,d}/.{vec->Nothing,pol->Nothing})==={} && (Head/@{e,f,g,h}/.{vec->Nothing,pol->Nothing})==={} && OrderedQ[{a,b,c,d}] && OrderedQ[{e,f,g,h}]*) :> epsilon[a,b,c,d]^(n-2) (- Plus@@((Signature[#]dot[a,#[[1]]]dot[b,#[[2]]]dot[c,#[[3]]]dot[d,#[[4]]])&/@Permutations[{a,b,c,d}]))
};*)


(* ::Text:: *)
(*Define some useful operations*)


ClearAll[conjugate,swap,decomp,weights,massdim,varpower,mompower];
(*swap angle and square brackets*)
conjugate[expr___] := expr /. {spA -> spS, spS -> spA, ap -> sp, sp -> ap} /.{momp[a_spA,p_vec,s_spS]:>momp[s,p,a]};
(*swap two labels / momenta*)
swap[expr___,i_,j_] := expr /. {spA[i] -> spA[j], spA[j] -> spA[i],spS[i] -> spS[j], spS[j] -> spS[i],vec[i] -> vec[j], vec[j] -> vec[i],pol[i] -> pol[j], pol[j] -> pol[i]}/.{momp[a_spA,p_vec,s_spS]:>momp[s,p,a]};
(*on monomials: decompose in a list of constituents (needed for functions below)*)(*NB leave isolated atomic expressions (e.g. integers) invariant*)
decomp[x_] /; AtomQ[x] := {x};
decomp[expr_] := Flatten[(expr/.Times->List)/.Power[x__,n_]:>ConstantArray[x,n]];
(*on monomials: count number of {square,angle} brackets for a given particle*)
weights[expr_,i_] := {Count[{decomp[expr]},spS[i],Infinity],Count[{decomp[expr]},spA[i],Infinity]}
(*extend to covariant objects*)
covweights[expr_,i_] := Count[{decomp[expr]},pol[i],Infinity];
(*on polynomials: apply to all monomials and check the same*)(*on monomials: give mass dimension, NB does not see factors of mass M (since not defined here)*)
massdim[expr_Plus,masses_List:{}] := If[Length@#==1,#[[1]],Print["Polynomial has non-uniform mass dimension."]]&@Union[massdim[#,masses]&/@(List@@expr)];
massdim[expr_,masses_List:{}] := 1/2 Count[{decomp[expr]},spS[_],Infinity]+1/2 Count[{decomp[expr]},spA[_],Infinity]+Count[{decomp[expr]},vec[_],Infinity]+Count[{decomp[expr]},m[_],Infinity]+Plus@@(Exponent[expr,#]&/@masses);
varpower[expr_,vars_List:{}] := Exponent[expr/.((#->\[Epsilon] #)&/@vars),\[Epsilon]];
mompower[expr_] := 1/2 Exponent[expr/.{vec[x_]:>\[Epsilon]^2 vec[x],spS[x_]:>\[Epsilon] spS[x],spA[x_]:>\[Epsilon] spA[x]},\[Epsilon]];


(* ::Text:: *)
(*Define a function to display variables nicely*)


display[expr_] := expr/.{pol->\[Epsilon],vec->P,dot->Dot,dp->Dot};


(* ::Section::Closed:: *)
(*Symbolic Expressions: Functions*)


(* ::Text:: *)
(*In this section we add some functions useful for manipulating symbolic expressions*)


(* ::Text:: *)
(*Define useful auxiliary functions*)


(*function for the spin-1 propagator structure*)
trDot[A_,B_,q_] := dot[A,B] - (dot[A,q]dot[B,q])/M^2;
(*function to swap two elements in a list*)
ClearAll[listSwap,seqLength];
listSwap[l_List,elem1_Integer,elem2_Integer]:=ReplacePart[l,{elem1->l[[elem2]],elem2->l[[elem1]]}];
(*function to compute the length of a sequence*)
seqLength[seq___] := Length@List@seq;
(*gives a condition for a symbolic expression to be zero, using vars as a basis*)
setzero[expr_,alt_Alternatives] := setzero[expr,Union@Cases[expr,alt,\[Infinity]]];
setzero[expr_,vars_List] := (#==0)&/@Union[Flatten[#["NonzeroValues"]&/@ Rest[CoefficientArrays[expr,vars]]]];
(*function to shift off-shell polarisation into momentum*)
longitShift[expr_,pol_,vec_]:=
If[Length@Cases[expr,pol,\[Infinity]]==2,1/2 Plus@@(ReplacePart[expr,#->vec]&/@Position[expr,pol,\[Infinity]]),expr/.{dot[x_,pol]^2:>dot[x,pol]dot[x,vec],dot[pol,x_]^2:>dot[pol,x]dot[vec,x],F[k_][x_,pol]^2:>F[k][x,pol]F[k][x,vec]}];
(*function to relabel polarisation vectors and momenta from a given label set to another*)
relabel[in_List,out_List] /; Length@in===Length@out := Join[Thread[Thread@pol[#1]->Thread@pol[#2]]&[in,out],Thread[Thread@vec[#1]->Thread@vec[#2]]&[in,out]];
(*function to remove a pole from an expression, if it is possible to do so by algebraic manipulation*)(*NB include all onshell and cut conditions in 'tobasis'*)
ClearAll[RemovePole];
RemovePole[expr_,pole_,tobasis_List] := Module[{\[Xi],polesub},polesub=Flatten@Solve[pole==\[Xi]//.tobasis];Expand@Together[(expr//.tobasis/.aa[_]:>0)/.polesub]/.\[Xi]->pole];(*NB aa[_]\[RuleDelayed]0 if the cut condition is defined with an extra parameter aa[_], where aa[_]\[RuleDelayed]0 gives the cut*)


(* ::Text:: *)
(*Define functions and replacement rules to perform index contraction and simplifications*)
(*NB: lorentzTr symmetrises BOTH sides before contracting. This could be improved, since we only need to symmetrise one side !!*)


(*OLD(*nice new function*)
ClearAll[dotTr];
dotTr[expr_,vars_List,reps_Integer]:=Module[{trvar,rules,trlist},
trvar = Select[Variables[expr],!Union@Cases[#,Alternatives@@vars,\[Infinity]]==={}&];
 rules = CoefficientRules[expr,trvar];
trlist = lorentzTr[#,vars,reps,reps]&/@(Times@@Power[trvar,#[[1]]]&/@rules);
Plus@@Times[trlist,#[[2]]&/@rules]
];*)
(*nice new function*)
ClearAll[dotTr];
dotTr[expr_,vars_List,reps_Integer]:=Module[{trvar,rules,trlist},
trvar = Select[Variables[expr],!Union@Cases[#,Alternatives@@vars,\[Infinity]]==={}&];
 rules = (Table[Length@Cases[#[[1]],i],{i,Length@trvar}]->#[[2]])&/@DeleteCases[Flatten[ArrayRules/@Rest[CoefficientArrays[expr,trvar]]],Rule[x_,0]];
trlist = lorentzTr[#,vars,reps,reps]&/@(Times@@Power[trvar,#[[1]]]&/@rules);
Plus@@Times[trlist,#[[2]]&/@rules]
];


ClearAll[lorentzTr,gammainsert,countvar,monomshift,shift,flipMajorana];
spinortrace = {dp[Ubar[-QQ],V[QQ]]->4,dp[Ubar[-QQ],A_,V[QQ]]:>0,dp[Ubar[-QQ],A_,B_,V[QQ]]:>4dot[A,B],dp[Ubar[-QQ],A_,B_,C_,V[QQ]]:>0};
lorentztrace = {
Derivative[indices__][_][__]/;!(Select[List@indices,#>1&]==={}):>0,
(*dot,dp,epsilon*)
Derivative[1,1][dot][a_,b_]:>$dim,
Derivative[i1_,i2_][dot][a_,b_]Derivative[j1_,j2_][dot][c_,d_]:>dot[a,c]^Boole[i1==0&&j1==0] dot[a,d]^Boole[i1==0&&j2==0] dot[b,c]^Boole[i2==0&&j1==0] dot[b,d]^Boole[i2==0&&j2==0],
Derivative[i1_,i2_][dot][a_,b_]^2:>dot[a,a]^Boole[i1==0] dot[b,b]^Boole[i2==0],
Derivative[i1_,i2_][dot][a_,b_]Derivative[0,indices__,0][dp][ub_,slashed__,v_]:>dp[ub,Sequence@@ReplacePart[List@slashed,Position[List@indices,1]->a^Boole[i1==0] b^Boole[i2==0]],v],
Derivative[0,left___,1,mid___,neigh_,1,right___,0][dp][ub_,slashed__,v_]:>
	2dp[ub,Sequence@@Delete[listSwap[List@slashed,-seqLength@right-2,seqLength@left+1],{{-seqLength@right-2},{-seqLength@right-1}}],v]
	-Derivative[0,left,1,mid,1,neigh,right,0][dp][ub,Sequence@@listSwap[List@slashed,-seqLength@right-1,-seqLength@right-2],v],
Derivative[0,left___,1,1,right___,0][dp][ub_,slashed__,v_]:>$dim dp[ub,Sequence@@Delete[List@slashed,{{Length@List@left+1},{Length@List@left+2}}],v],
Derivative[i1_,i2_][dot][a_,b_]Derivative[indices__][epsilon][terms__]:>epsilon[Sequence@@ReplacePart[List@terms,Position[List@indices,1]->a^Boole[i1==0] b^Boole[i2==0]]],
Derivative[left___,1,mid___,1,right___][epsilon][___]:>0,
(*odot,epsilon*)
Derivative[1,1][odot][a_,b_]:>$odim,
Derivative[i1_,i2_][odot][a_,b_]Derivative[j1_,j2_][odot][c_,d_]:>odot[a,c]^Boole[i1==0&&j1==0] odot[a,d]^Boole[i1==0&&j2==0] odot[b,c]^Boole[i2==0&&j1==0] odot[b,d]^Boole[i2==0&&j2==0],
Derivative[i1_,i2_][odot][a_,b_]^2:>odot[a,a]^Boole[i1==0] odot[b,b]^Boole[i2==0],
Derivative[i1_,i2_][odot][a_,b_]Derivative[indices__][epsilon][terms__]:>epsilon[Sequence@@ReplacePart[List@terms,Position[List@indices,1]->a^Boole[i1==0] b^Boole[i2==0]]],
Derivative[left___,1,mid___,1,right___][epsilon][___]:>0,
(*dot+odot*)
Derivative[i1_,i2_][odot][a_,b_]Derivative[j1_,j2_][dot][c_,d_]:>odot[a,c]^Boole[i1==0&&j1==0] odot[a,d]^Boole[i1==0&&j2==0] odot[b,c]^Boole[i2==0&&j1==0] odot[b,d]^Boole[i2==0&&j2==0],
(*field strengths*)
(*Derivative[i1_,i2_][dot][a_,b_]Derivative[j1_,j2_][F[l_]][c_,d_]:>F[l][c,a]^Boole[i1==0&&j1==0] F[l][a,d]^Boole[i1==0&&j2==0] F[l][c,b]^Boole[i2==0&&j1==0] F[l][b,d]^Boole[i2==0&&j2==0],
Derivative[i1_,i2_][dot][a_,b_]Derivative[j1_,j2_][tFF[l1_,l2_]][c_,d_]:>tFF[l1,l2][c,a]^Boole[i1==0&&j1==0] tFF[l1,l2][a,d]^Boole[i1==0&&j2==0] tFF[l1,l2][c,b]^Boole[i2==0&&j1==0] tFF[l1,l2][b,d]^Boole[i2==0&&j2==0],
Derivative[1,1][tFF[l1_,l2_]][a_,b_]:>-ttFF[l1,l2],
Derivative[i1_,i2_][F[l1_]][a_,b_]Derivative[j1_,j2_][F[l2_]][c_,d_]:>(-tFF[l1,l2][a,c])^Boole[i1==0&&j1==0] (tFF[l1,l2][a,d])^Boole[i1==0&&j2==0] (tFF[l1,l2][b,c])^Boole[i2==0&&j1==0] (-tFF[l1,l2][b,d])^Boole[i2==0&&j2==0]*)
Derivative[i1_,i2_][dot][a_,b_]Derivative[j1_,j2_][F[l_]][c_,d_]:>Which[i1==0&&j1==0,F[l][c,a],i1==0&&j2==0,F[l][a,d],i2==0&&j1==0,F[l][c,b],i2==0&&j2==0,F[l][b,d]],
Derivative[i1_,i2_][dot][a_,b_]Derivative[j1_,j2_][tFF[l1_,l2_]][c_,d_]:>Which[i1==0&&j1==0,tFF[l1,l2][c,a],i1==0&&j2==0,tFF[l1,l2][a,d],i2==0&&j1==0,tFF[l1,l2][c,b],i2==0&&j2==0,tFF[l1,l2][b,d]],
Derivative[1,1][tFF[l1_,l2_]][a_,b_]:>-ttFF[l1,l2],
Derivative[i1_,i2_][F[l1_]][a_,b_]Derivative[j1_,j2_][F[l2_]][c_,d_]:>Which[i1==0&&j1==0,(-tFF[l1,l2][a,c]),i1==0&&j2==0,(tFF[l1,l2][a,d]),i2==0&&j1==0,(tFF[l1,l2][b,c]),i2==0&&j2==0,(-tFF[l1,l2][b,d])]
};
spinorjoin[mom1_,mom2_] := {dp[ub_,slashed1___,V[-mom1]]dp[Ubar[-mom2],slashed2___,v_]:>dp[ub,slashed1,slashed2,v],dp[ub_,slashed1___,V[mom2]]dp[Ubar[mom1],slashed2___,v_]:>dp[ub,slashed1,slashed2,v]};
spinorjoin2[mom_] := {dp[ub_,slashed1___,V[mom]]dp[Ubar[-mom],slashed2___,v_]:>dp[ub,slashed1,slashed2,v]};
gammainsert[QQ_] := {
(*from right*)
Derivative[0,indices__,0][dp][ub_,left___,pol[QQ],neigh_,right___,V[QQ]]:>2dp[ub,left,right,neigh,V[QQ]] - Derivative[0,Sequence@@RotateRight[List@indices,1],0][dp][ub,left,neigh,pol[QQ],right,V[QQ]],
Derivative[0,indices__,0][dp][ub_,rest___,pol[QQ],V[QQ]]:>4 dp[ub,rest,V[QQ]],
Derivative[i1_,i2_][dot][a_,b_]dp[ub_,slashed___,V[QQ]]:>dp[ub,slashed,a^Boole[i1==0] b^Boole[i2==0],V[QQ]],
(*from left*)
Derivative[0,indices__,0][dp][Ubar[QQ],left___,neigh_,pol[QQ],right___,v_]:>2dp[Ubar[QQ],neigh,left,right,v] - Derivative[0,Sequence@@RotateLeft[List@indices,1],0][dp][Ubar[QQ],left,pol[QQ],neigh,right,v],
Derivative[0,indices__,0][dp][Ubar[QQ],pol[QQ],rest___,v_]:>4 dp[Ubar[QQ],rest,v],
Derivative[i1_,i2_][dot][a_,b_]dp[Ubar[QQ],slashed___,v_]:>dp[Ubar[QQ],a^Boole[i1==0] b^Boole[i2==0],slashed,v]
};
lorentzTr[expr_,vars_List,reps_Integer,pols_Integer:2,samepols_:False] := With[{join = Expand@D[#,Sequence@@vars]//.lorentztrace&},(*Print[StringForm["Polarisation vectors: ``", pols]];*) If[samepols,Product[(pols-2k)!/(pols-2k+2)!,{k,1,reps}],1/(pols!)^2] Nest[join,expr,reps]];
(*function to count the power of a variable in a monomial made up of dot[...] and dp[...]*)
(*OPTION 1:*)(*NB does not work with epsilon...*)(*countvar[expr_,var_] := Exponent[expr/.{dot[left___,var,right___]:>var^(Length@Cases[{left},var]+Length@Cases[{right},var]+1),dp[left___,var,right___]:>var^(Length@Cases[{left},var]+Length@Cases[{right},var]+1),epsilon[left___,var,right___]:>var^(Length@Cases[{left},var]+Length@Cases[{right},var]+1)},var];*)
(*OPTION 2:*)countvar[expr_,var_] := Exponent[expr/.var->\[Epsilon] var,\[Epsilon]];
(*function to shift a field/polarisation by some vector or variable*)(*improved version of longitShift, valid for any spin*)
monomshift[expr_,pol_,vec_]:=1/Max[1,countvar[expr,pol]] Expand[D[expr,pol]D[dot[pol,vec],pol]]//.lorentztrace;
(*old shift: shift[expr_,pol_,vec_] := If[PolynomialQ[#,Union@Cases[#,_dp|_dot,\[Infinity]]]&@expr,If[Head@Expand@expr === Plus,monomshift[#,pol,vec]&/@Expand[expr],monomshift[expr,pol,vec]],Print["Non-polynomial expression"]];*)
shift[expr_,pol_,vec_] := D[expr,pol]/.\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", "___", "]"}], "[", "dot", "]"}], "[", 
RowBox[{"left___", ",", "pol", ",", "right___"}], "]"}], ":>", 
RowBox[{"dot", "[", 
RowBox[{"left", ",", "vec", ",", "right"}], "]"}]}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\);
(*function to use an identity of Majorana fermions to flip Ubar and V*)
flipMajorana[expr_] := expr/.{
dp[Ubar[A_],Gamma5,V[B_]] :> -dp[Ubar[B],Gamma5,V[A]],
dp[Ubar[A_],slashed___,V[B_]] :> -(-1)^Length@List@slashed dp[Ubar[B],Sequence@@Reverse@List@slashed,V[A]]
};


(* ::Text:: *)
(*Define useful functions for ansatz construction*)


ClearAll[dotproducts,modweights,dpAnsatz,dpAnsatzSpecialize,dptobasis];
(*compute all possible dot products containing the elements of a list*)
dotproducts[1] := 1;
dotproducts[terms_List] := Union@(Times@@@Map[Sort@(dot@@#)&,Partition[#,2]&/@Permutations@terms,{2}])
(*subtract from the total weights the terms that have already been used*)
modweights[weights_List,subtracted_List] := List@@((Times@@weights)/(Times@@subtracted))/. Power[var_, k_] :> Sequence @@ Table[var, k];
(*define all possible ansatz terms, given the total (covariant) weights and possible on-shell rules, with a given number of gammas*)
(*Example: dpAnsatz[Join[ansatzweights,{vec[q]}],3,ansatzrules]*)
dpAnsatz[covweights_List,gammas_Integer,rules_List:{}] := With[{agplist=Subsets[Union@covweights, {gammas}]},
	Flatten@Times[
		DeleteCases[dotproducts/@(modweights[covweights,#]&/@agplist)/.rules,0,\[Infinity]],
		dp[Ubar[x],AGP[Sequence@@#],V[y]]&/@agplist
	]
]
(*take in a list generated by dpAnsatz and substitute in all possible values of some specified variables (eg momenta)*)
(*Example: dpAnsatzSpecialize[dpAnsatz[CTweights~Join~{vec[q1],vec[q2]},0,CTrules],{vec[q1],vec[q2]},{vec[1],vec[2],vec[3]},CTrules]*)
dpAnsatzSpecialize[terms_List,vars_List,options_List,rules_:{}] := DeleteCases[Union[Flatten[terms/.#&/@(Thread[vars->#]&/@DeleteDuplicates[Sort/@Tuples[options,Length@vars]])]/.rules],0];
(*function to reduce some Dirac spinor expression to a basis, given the rules*)
dptobasis[expr_,tobasis_] := FixedPoint[dpSimplify[#//.tobasis]&,expr];


(*alternative function to dotproducts*)
dotprod[1] := 1;
dotprod[terms_List] := Module[{explist={},poscond={},powcond={},expsol={}},
(*find all individual dot product exponents*)
explist = DeleteDuplicates[ex@@@Subsets[terms,{2}]];
(*find positivity conditions*)
poscond = #>=0&/@explist;
(*find total power condition*)
powcond = Function[x,Plus@@(Length@Cases[#,x,\[Infinity]]#&/@explist)==Length@Cases[terms,x]]/@DeleteDuplicates[terms];
(*find solutions*)
expsol = Solve[Join[poscond,powcond],Integers];
(*write monomials*)
Times@@(explist/.ex[x_,y_]:>dot[x,y]^ex[x,y])/.expsol
];


(* ::Text:: *)
(*Define function to set masses to some value. Automatically unprotects and protects mass head*)


ClearAll[massSet];
massSet[legs_List,mass_List] :=(Unprotect[m];ClearAll[m];Set[Evaluate[m/@legs],mass];Protect[m];)


(* ::Chapter::Closed:: *)
(*Numerics*)


(* ::Section::Closed:: *)
(*Massive spinor-helicity*)


(* ::Text:: *)
(*Define global assumptions*)


$Assumptions=M>0 && M\[Element]Reals;


(* ::Text:: *)
(*Define momentum matrices. Work with \[Eta]  = (1,-1,-1,-1).*)
(*Note that pA = Subscript[p, \[Mu]] \[Sigma]^\[Mu] and pS = Subscript[p, \[Mu]] \!\(\*OverscriptBox[\(\[Sigma]\), \(_\)]\)^\[Mu].*)


LC = {{0,1},{-1,0}}; (* Levi Civita *)
pA= M{{a,b},{c,(1+b c)/a}}; (* on-shell fixed by determinant *)
pS = -Transpose[LC . pA . LC];
momS[pA_]:=-Transpose[LC . pA . LC];


(* ::Text:: *)
(*Find Weyl spinors (method given in my MSH notes). Note that pA = Outer[Times,\[Lambda],\!\(\*OverscriptBox[\(\[Lambda]\), \(~\)]\)] + Outer[Times,\[Eta],\!\(\*OverscriptBox[\(\[Eta]\), \(~\)]\)]. *)
(*We can also define matrices spinor = (\[Lambda],\[Eta]) and tilda = Transpose[(\!\(\*OverscriptBox[\(\[Lambda]\), \(~\)]\),\!\(\*OverscriptBox[\(\[Eta]\), \(~\)]\))] so that pA = spinor.tilda.*)


lambda = Sqrt[M]{{Sqrt[a],c/Sqrt[a]},{Sqrt[a],b/Sqrt[a]}};
eta = Sqrt[M]{{0,1/Sqrt[a]},{0,1/Sqrt[a]}};
myeta = Sqrt[M]{{0,1/Sqrt[a]},{0,1/Sqrt[a]}};


spin=If[RationalNumerics===False,Sqrt[M]{{Sqrt[a],0},{c/Sqrt[a],1/Sqrt[a]}},M{{a,0},{c,1}}];
tilda=If[RationalNumerics===False,Sqrt[M]{{Sqrt[a],b/Sqrt[a]},{0,1/Sqrt[a]}},M{{a,b},{0,1}}];


(* ::Text:: *)
(*Define spinor brackets \[InvisibleComma]\[LeftAngleBracket]1^A 2^B\[RightAngleBracket] and [1^A 2^B]*)


squareprod[spin1_,spin2_]:=-Transpose[spin1] . LC . spin2;
angleprod[tilda1_,tilda2_]:=-LC . tilda1 . LC . Transpose[tilda2] . LC;
momprod[spin_,mom_,tilda_]:=Transpose[spin] . (-LC) . mom . LC . Transpose[tilda] . (-LC);


(* ::Text:: *)
(*Now check spinor relations*)


(* determinants *)
{Det[spin],Det[tilda]}
(* completeness *)
Simplify[spin . tilda-pA]
(* Dirac *)
Simplify[-Transpose[spin] . LC . pA+M LC . tilda]


(* ::Text:: *)
(*Now check massless limit. This should give the same matrices and spinors as defined in Section 2.*)


massless = {a->\[Alpha]1/M,b->(A1 \[Alpha]1)/M,c->\[Gamma]1/M};
Simplify[pA /. massless] /. M->0
Simplify[lambda /. massless] /. M->0
Simplify[myeta /. massless] /. M->0


(* ::Text:: *)
(*Define Dirac spinors (Little group index as row index)*)


(*spinors*)
dirac = Table[Flatten[{Transpose[spin][[i]],(-LC . tilda . LC)[[i]]}],{i,1,2}];
diracbar = Table[Flatten[{(-LC . Transpose[spin] . LC)[[i]],tilda[[i]]}],{i,1,2}];
pD = KroneckerProduct[{{0,1},{0,0}},pA]+KroneckerProduct[{{0,0},{1,0}},momS[pA]];


(*checks*)
(*dirac eq*)
(pD . #)&/@dirac - M dirac//Simplify
(# . pD)&/@diracbar - M diracbar//Simplify
(*conjugation*)
conj = {b->c,c->b}; (*this reduces to complex conjugation on real kinematics*)
gamma0 = KroneckerProduct[{{0,1},{1,0}},{{1,0},{0,1}}];
(# . gamma0)&/@(dirac/.conj)-diracbar//Simplify


(* ::Section::Closed:: *)
(*Massless spinor-helicity*)


(* ::Text:: *)
(*Define momentum matrices*)


nullA={{\[Alpha],A \[Alpha]},{\[Gamma],A \[Gamma]}};
nullS=-Transpose[LC . nullA . LC];


(* ::Text:: *)
(*Define spinors*)


square=If[RationalNumerics===False,{Sqrt[\[Alpha]],\[Gamma]/Sqrt[\[Alpha]]},{\[Alpha],\[Gamma]}];
angle=If[RationalNumerics===False,{Sqrt[\[Alpha]],A Sqrt[\[Alpha]]},{1,A}];


(* ::Text:: *)
(*Check relations*)


(* Dirac *)
nullS . square
(* completeness for nullS *)
Outer[Times,LC . angle,LC . square]-nullS


(* ::Text:: *)
(*Define spinor brackets \[InvisibleComma]\[LeftAngleBracket]2 4^B\[RightAngleBracket], [1^A 3],  \[InvisibleComma]\[LeftAngleBracket]2 4\[RightAngleBracket], [1 3], ...*)


mixsquareprod[spin_,square_]:=-Transpose[spin] . LC . square;
mixangleprod[angle_,tilda_]:=-angle . LC . Transpose[tilda] . LC;
nullsquareprod[square1_,square2_]:=-square1 . LC . square2;
nullangleprod[angle1_,angle2_]:=angle1 . LC . angle2;
nullmomprod[square1_,mom_,angle2_]:=square1 . (-LC) . mom . LC . angle2;


(* ::Text:: *)
(*Define useful functions*)


mydot[A1_,A2_]:=-(1/2)Tr[Transpose[A1] . LC . A2 . LC]; 


(* ::Text:: *)
(*Define covariant polarisation vectors*)


ClearAll[pol0A,tpol0A];
tpol0A={{p01,p02},{p03,p04}};
tpolcond=Solve[{mydot[tpol0A,nullA]==0,mydot[tpol0A,tpol0A]==0},{p01,p02,p03,p04},Complexes]
{pol0A1=tpol0A/.tpolcond[[1]],pol0A2=tpol0A/.tpolcond[[2]]}


(* ::Section::Closed:: *)
(*Additional Functions*)


(* ::Text:: *)
(*Define Minkowski metric*)


mink = DiagonalMatrix[{1,-1,-1,-1}];


(* ::Text:: *)
(*Define an auxiliary function to convert spinors etc defined in this code into those for some given momentum*)


MassiveConv[pA_]:={a->M^-1 pA[[1,1]],b ->M^-1 pA[[1,2]],c ->M^-1 pA[[2,1]]};
MasslessConv[nullA_]:={\[Alpha]->nullA[[1,1]],\[Gamma] ->nullA[[2,1]],A ->nullA[[1,2]]/nullA[[1,1]]};


(* ::Text:: *)
(*Define functions that take a momentum matrix pA and returns outgoing Weyl and Dirac spinors. Include a variable to contract little group indices.*)


AngleSp[pA_]:=With[{convert=MasslessConv[pA]},angle/.convert//Simplify];
SquareSp[pA_]:=With[{convert=MasslessConv[pA]},square/.convert//Simplify];
WeylA[pA_,u_]:=With[{convert=MassiveConv[pA]},(u . LC . tilda)/.convert/.{M->Sqrt[Det[pA]]}//Simplify];
WeylS[pA_,u_]:=With[{convert=MassiveConv[pA]},(spin . u)/.convert/.{M->Sqrt[Det[pA]]}//Simplify];
DiracV[pA_,u_]:=With[{convert=MassiveConv[pA]},(u . Table[Flatten[{Transpose[spin][[i]],-(-LC . tilda . LC)[[i]]}],{i,1,2}])/.convert/.{M->Sqrt[Det[pA]]}//Simplify];
DiracUbar[pA_,u_]:=With[{convert=MassiveConv[pA]},(u . LC . Table[Flatten[{(-LC . Transpose[spin] . LC)[[i]],tilda[[i]]}],{i,1,2}])/.convert/.{M->Sqrt[Det[pA]]}//Simplify];


(* ::Text:: *)
(*Define functions that create polarisation vector matrices*)


MassivePol[pA_,u_]:=With[{convert=MassiveConv[pA]},(M^-1 Outer[Times,(spin/.convert) . u,u . LC . (tilda/.convert)])(*/.convert*)/.{M->Sqrt[Det[pA]]}//Simplify];
MinusPol[nullA_,xi_]:=With[{convert=MasslessConv[nullA]},(Outer[Times,xi,angle]/nullsquareprod[xi,square])/.convert//Simplify];(*|xi]*)
PlusPol[nullA_,psi_]:=With[{convert=MasslessConv[nullA]},(Outer[Times,square,psi]/nullangleprod[psi,angle])/.convert//Simplify];(*<psi|*)


(* ::Text:: *)
(*Define: gamma matrices (and antisymmetrised products), function that takes in A \dot \sigma and returns A^\mu, function that takes in A \dot \sigma and returns A \dot \gamma*)


gamma[i_] /; MemberQ[Range[0,3],i] := KroneckerProduct[{{0,1},{0,0}},PauliMatrix[i]]+KroneckerProduct[{{0,0},{1,0}},momS[PauliMatrix[i]]]//Simplify;
gamma[i_] /; i==5 := I gamma[0] . gamma[1] . gamma[2] . gamma[3];
gamma2[i_,j_]:=Signature[{i,j}] 1/2! Plus@@((Signature[#]gamma[#[[1]]] . gamma[#[[2]]])&/@Permutations[{i,j}]);
gamma3[i_,j_,k_]:=Signature[{i,j,k}] 1/3! Plus@@((Signature[#]gamma[#[[1]]] . gamma[#[[2]]] . gamma[#[[3]]])&/@Permutations[{i,j,k}]);
Vector[pA_]:=1/2 Table[Tr[pA . momS[PauliMatrix[i]]],{i,0,3}]//Simplify;
dotgamma[pA_]:=KroneckerProduct[{{0,1},{0,0}},pA]+KroneckerProduct[{{0,0},{1,0}},momS[pA]]//Simplify;


(* ::Text:: *)
(*Define a function to check that a set of spinors and their momenta are compatible*)


CheckMassive[spin_,pA_,tilda_]:=With[{M=Simplify[Sqrt[Det[pA]]]},If[Simplify[pA . LC . tilda - M spin] == {0,0} && Simplify[momS[pA] . spin - M LC . tilda] == {0,0},True,False]];
CheckMassless[square_,pA_,angle_]:=If[Simplify[pA . LC . angle] == {0,0} && Simplify[momS[pA] . square] == {0,0} && Simplify[Outer[Times,square,angle] - pA] == {{0,0},{0,0}},True,False];


(* ::Section::Closed:: *)
(*Numerics*)


(* ::Subsection::Closed:: *)
(*Basics*)


(* ::Text:: *)
(*Define functions to evaluate the above symbolic expressions numerically*)


(*variable to switch to conventions of 2107.14779*)(*default to false*)
ConventionFix = False;


(*first a function to give numeric polarisation vectors*)
(*NB definition below may be not valid for some cut. Hence in that case return InvalidPOL variable*)
(*EXAMPLE: massive = {A,B,C,...} , massless = {{a,h_a},{b,h_b},{c,h_c},...}}*)
ClearAll[Numgen];
Numgen[fun_,massive_List,massless_List,refmax_Integer:10] := 
{
(POL[#] = If[ConventionFix,Sqrt[2],1]MassivePol[p[#]//fun,u[#]//fun])&/@massive,
(POLB[#] = If[ConventionFix,Sqrt[2],2]MassivePol[p[#]//fun,ub[#]//fun])&/@massive,
If[ConventionFix,
	(POL[#[[1]]] = Quiet@Check[If[#[[2]]==1,Sqrt[2]MinusPol[p[#[[1]]]//fun,{1,-2}]+Sqrt[2]ga[#[[1]]]((p[#[[1]]]//fun)/nullsquareprod[{1,-2},SquareSp[p[#[[1]]]//fun]]),-Sqrt[2]PlusPol[p[#[[1]]]//fun,{1,-2}]-Sqrt[2]ga[#[[1]]]((p[#[[1]]]//fun)/nullangleprod[{1,-2},AngleSp[p[#[[1]]]//fun]])],InvalidPOL[#[[1]]]])&/@massless,
	(POL[#[[1]]] = Quiet@Check[
	Which[#[[2]]==1,PlusPol[p[#[[1]]]//fun,{1,-2}]+ga[#[[1]]]((p[#[[1]]]//fun)/nullangleprod[{1,-2},AngleSp[p[#[[1]]]//fun]]),#[[2]]==-1,MinusPol[p[#[[1]]]//fun,{1,-2}]+ga[#[[1]]]((p[#[[1]]]//fun)/nullsquareprod[{1,-2},SquareSp[p[#[[1]]]//fun]]),#[[2]]==0,zp0[#[[1]]]PlusPol[p[#[[1]]]//fun,{1,-2}]+zm0[#[[1]]]MinusPol[p[#[[1]]]//fun,{1,-2}]+ga[#[[1]]](p[#[[1]]]//fun)]
	,InvalidPOL[#[[1]]]])&/@massless
],
POL[ref] = {{pra,prb},{prc,prd}},
POL[tref] = {{pra,prb},{prc,(prb prc)/pra}},
Do[POL[ref[i]] = {{ra[i],rb[i]},{rc[i],rd[i]}},{i,1,refmax}],
Do[POL[tref[i]] = {{ra[i],rb[i]},{rc[i],(rb[i] rc[i])/ra[i]}},{i,1,refmax}]
};


(*then a dictionary between symbolic and numeric expressions*)
(*EXAMPLE: massive = {1,2,3,4}*)
ClearAll[Numdict];
Numdict[expr_,fun_,massive_List] := 
With[ 
{
slashed = (#/.{pol[k_]:>dotgamma[POL[k]],polb[k_]:>dotgamma[POLB[k]],vec[k_]:>dotgamma[p[k]//fun],Gamma5->gamma[5]})&,
tovector = (#/.{pol[k_]:>Vector[POL[k]],polb[k_]:>Vector[POLB[k]],vec[k_]:>Vector[p[k]//fun]})&(*,
fnum = fun[mydot[p[#1]//fun,#2]]fun[mydot[POL[#1],#3]]-fun[mydot[POL[#1],#2]]fun[mydot[p[#1]//fun,#3]]&*)
},
expr /.
{
(*COVARIANT EXPRESSIONS*)
dot[vec[i_],vec[j_]]:>fun[mydot[p[i]//fun,p[j]//fun]],
dot[pol[i_],pol[j_]]:>fun[mydot[POL[i],POL[j]]],
dot[polb[i_],polb[j_]]:>fun[mydot[POLB[i],POLB[j]]],
dot[pol[i_],vec[j_]]:>fun[mydot[POL[i],p[j]//fun]],
dot[pol[i_],polb[j_]]:>fun[mydot[POL[i],POLB[j]]],
dot[polb[i_],vec[j_]]:>fun[mydot[POLB[i],p[j]//fun]],
M->fun[M],
Sequence@@Union@Table[m[i]->fun[m[i]],{i,massive}],

(*DIRAC SPINOR EXPRESSIONS*)
dp[Ubar[i_],V[j_]]:>fun[DiracUbar[p[i]//fun,u[i]] . DiracV[p[j]//fun,u[j]]],
dp[Ubar[i_],slash__,V[j_]]:>fun[DiracUbar[p[i]//fun,u[i]] . (Dot@@slashed/@List@slash) . DiracV[p[j]//fun,u[j]]],

(*WEYL SPINOR EXPRESSIONS*)
ap[spA[i_],spA[j_]]:>fun[nullangleprod[If[MemberQ[massive,i],WeylA[p[i]//fun,u[i]],AngleSp[p[i]//fun]],If[MemberQ[massive,j],WeylA[p[j]//fun,u[j]],AngleSp[p[j]//fun]]]],
sp[spS[i_],spS[j_]]:>fun[nullsquareprod[If[MemberQ[massive,i],WeylS[p[i]//fun,u[i]],SquareSp[p[i]//fun]],If[MemberQ[massive,j],WeylS[p[j]//fun,u[j]],SquareSp[p[j]//fun]]]],
momp[spS[i_],vec[x_],spA[j_]]:>fun[nullmomprod[If[MemberQ[massive,i],WeylS[p[i]//fun,u[i]],SquareSp[p[i]//fun]],p[x]//fun,If[MemberQ[massive,j],WeylA[p[j]//fun,u[j]],AngleSp[p[j]//fun]]]],

(*LEVI-CIVITA*)
epsilon[A_,B_,C_,D_]:>TensorContract[TensorProduct[LeviCivitaTensor[4],mink . tovector@A,mink . tovector@B,mink . tovector@C,mink . tovector@D],{{1,5},{2,6},{3,7},{4,8}}]

(*FIELD STRENGTHS*)
(*F[a_][vec[i_],vec[j_]]:>0,
F[a_][pol[i_],vec[j_]]:>0,
F[a_][vec[i_],pol[j_]]:>0,
F[a_][pol[i_],pol[j_]]:>0*)
}
];


(* ::Text:: *)
(*Function to evaluate a list of building blocks several times and make a SQUARE matrix of evaluations*)


(*function to evaluate numerics once*)
(*EXAMPLE: toNum[terms,numfun,FFnum,{1,2},{{3,-1},{4,1}}];*)
ClearAll[toNum];
toNum[terms_List,fun_,num_,massive_List,massless_List] := With[{},
Numgen[fun[#,num]&,massive,massless](*create polarisation vectors*);
Numdict[terms,fun[#,num]&,massive](*/.{ga[3]->RandomInteger[max],ga[4]->RandomInteger[max]}*)
]


(*function to build a matrix of numerics*)
(*define prime = max number we consider*)
$P =(* NextPrime[2^31,-1]*)9600000001;(*prime of form 8k+1, to have both -1 and 2 quadratic residues*)
(*EXAMPLE: NumEvalMatrix[contactanslist,numfun,FFvars,{1,2},{{3,-1},{4,1}},1]*)
(*rational / finite fields*)
ClearAll[NumEvalMatrix,NumEvalMatrixFP];
NumEvalMatrix[terms_List,fun_,vars_,massive_List,massless_List,rep_:0] := Module[{tempnum={},matrix={},reps=If[rep==0,Length@terms,rep]},
	matrix = 
	Reap[
		Do[
			tempnum=(#->RandomInteger[{0,$P-1}])&/@vars;
			Sow[toField/@toNum[terms,fun,tempnum,massive,massless]];
		,{i,1,reps}
		]
	][[2,1]];
	matrix
]
(*floating point numbers*)
NumEvalMatrixFP[terms_List,fun_,vars_,massive_List,massless_List,rep_:0,prec_:1000] := Module[{tempnum={},matrix={},reps=If[rep==0,Length@terms,rep]},
	matrix = 
	Reap[
		Do[
			tempnum=(#->RandomInteger[{0,$P-1}])&/@vars;
			Sow[N[#,prec]&/@toNum[terms,fun,tempnum,massive,massless]];
		,{i,1,reps}
		]
	][[2,1]];
	matrix
]


(* ::Text:: *)
(*Create a function taking in a matrix in row reduced form and returning the position (columns) of the leading 1s*)


ClearAll[BasisPos];
(*OLD:*)(*BasisPos[rowred_List] := Position[#,1,1,1][[1,1]]&/@DeleteCases[rowred,Table[0,{i,1,Length@rowred}]];*)
BasisPos[rowred_List] := If[Union[#]==={0},Nothing,Position[#,1,1,1][[1,1]]]&/@rowred;


(* ::Text:: *)
(*Function to match two expressions together numerically*)


ClearAll[MatchNum];
MatchNum[ansatz_,target_,fun_,vars_List,massive_List,massless_List,reps_Integer,maxnum_:1000] := Module[{equations = {},tempnum},
Do[
tempnum = (#->RandomInteger[maxnum])&/@vars;(*define temporary numerics*)
Numgen[fun[#,tempnum]&,massive,massless];(*create polarisation vectors*)
AppendTo[equations,Quiet@Check[(Numdict[ansatz,fun[#,tempnum]&,massive] == Numdict[target,fun[#,tempnum]&,massive])/.{ga[3]->RandomInteger[max],ga[4]->RandomInteger[max]},Nothing]];(*create equation for the chosen numerics*)
ClearAll[tempnum];
,{i,1,reps}];
equations
]


(* ::Subsection::Closed:: *)
(*Finite Fields*)


(* ::Text:: *)
(*Basics*)


(*define finite field numerics*)
$P =(* NextPrime[2^31,-1]*)9600000001;(*prime of form 8k+1, to have both -1 and 2 quadratic residues*)
(*from rational to field*)
ClearAll[toField,toRational];
toField[Rational[r_,s_],P_:$P] := Mod[Mod[r,P]*ModularInverse[s,P],P];
toField[n_Integer,P_:$P] := Mod[n,P];
(*from field to rational*)
toRational[a_,P_:$P] := Rational@@First@Sort[LatticeReduce[{{a,1},{P,0}}],Norm[#1]<Norm[#2]&];
(*Create a function taking in a matrix in row reduced form and returning the position (columns) of the leading 1s*)
ClearAll[BasisPos];
BasisPos[rowred_List] := If[Union[#]==={0},Nothing,Position[#,1,1,1][[1,1]]]&/@rowred;


(* ::Text:: *)
(*Functions for Compton kinematics*)


(*finite field functions*)
(*creates a set of numerics rules for individual dot products*)
ClearAll[dotNumCompton];
dotNumCompton[dots_,numfun_,FFvars_,reps_] := With[{normdots = dots//.Frule},
Thread[(dots/.{dot->d,pol->e,vec->pp,ap->nap,sp->nsp,momp->nmomp,spS->nS,spA->nA,F->nF,tFF->ntFF,ttFF->nttFF})->#]&/@Drop[RandomSample@Join[
NumEvalMatrix[normdots,numfun,FFvars,{1,2},{{3,1},{4,1}},Ceiling[reps/4]],
NumEvalMatrix[normdots,numfun,FFvars,{1,2},{{3,1},{4,-1}},Ceiling[reps/4]],
NumEvalMatrix[normdots,numfun,FFvars,{1,2},{{3,-1},{4,-1}},Ceiling[reps/4]],
NumEvalMatrix[normdots,numfun,FFvars,{1,2},{{3,-1},{4,1}},Ceiling[reps/4]]],4Ceiling[reps/4]-reps]
];
dotNumCompton[dots_,numfun_,FFvars_,reps_,hels_] := With[{normdots = dots//.Frule},
Thread[(dots/.{dot->d,pol->e,vec->pp,ap->nap,sp->nsp,momp->nmomp,spS->nS,spA->nA,F->nF,tFF->ntFF,ttFF->nttFF})->#]&/@
NumEvalMatrix[normdots,numfun,FFvars,{1,2},hels,reps]
];
(*use the numeric rules to build a matrix from an ansatz list*)
ClearAll[ansNumerics]
ansNumerics[list_,dotrules_] := Map[toField,Reap[Do[
Clear[d,M,nap,nsp,nmomp,nF,ntFF,nttFF];
dotrules[[j]]/.Rule->Set;
Sow[list/.{dot->d,pol->e,vec->pp,ap->nap,sp->nsp,momp->nmomp,spS->nS,spA->nA,F->nF,tFF->ntFF,ttFF->nttFF}];Clear[d,M,nap,nsp,nmomp,nF,ntFF,nttFF];,{j,Length@dotrules}]][[2,1]],{2}];
(*extract linearly independent ansatz structures*)
ClearAll[ansIndep];
ansIndep[anslist_,ansmat_] := anslist[[#]]&/@BasisPos[RowReduce[ansmat,Modulus->$P]];
(*use the functions (dotNumCompton,ansNumerics,ansIndep) to take in an ansatz list and return an independent ansatz list*)
ClearAll[indepFF];
indepFF[{},numfun_,FFvars_,reps_Integer:-1] := {};
indepFF[anslist_,numfun_,FFvars_,reps_:-1] := Module[{dots = Variables[anslist],NN = If[reps===-1,Length@anslist,reps],dotrules,ansnummat},
dotrules = dotNumCompton[dots,numfun,FFvars,NN];
ansnummat = ansNumerics[anslist,dotrules];
(*If[!SquareMatrixQ[ansnummat],Return["Evaluation matrix is not square"]];*)
ansIndep[anslist,ansnummat]
];
indepFF[anslist_,numfun_,FFvars_,hels_List,reps_Integer:-1] := Module[{dots = Variables[anslist],NN = If[reps===-1,Length@anslist,reps],dotrules,ansnummat},
dotrules = dotNumCompton[dots,numfun,FFvars,NN,hels];
ansnummat = ansNumerics[anslist,dotrules];
(*If[!SquareMatrixQ[ansnummat],Return["Evaluation matrix is not square"]];*)
ansIndep[anslist,ansnummat]
];
(*use the functions (dotNumCompton,ansNumerics) to take in an ansatz plus a list of conditions and return the general solution*)
ClearAll[solveFF];
solveFF[anslist_,{},numfun_,FFvars_,reps_] := {};
solveFF[anslist_,condlist_,numfun_,FFvars_,reps_] := Module[{dots = Variables[condlist],dotrules,ansnummat,nullspace},
dotrules = dotNumCompton[dots,numfun,FFvars,reps];
ansnummat = Flatten[ansNumerics[#,dotrules]&/@condlist,1];
nullspace = Map[toRational,NullSpace[ansnummat,Modulus->$P],{2}];
Sum[cC[i]nullspace[[i]] . anslist,{i,1,Length@nullspace}]
];
(*use the functions (dotNumCompton,ansNumerics) to match an ansatz to a fixed target expression*)
ClearAll[matchFF];
matchFF[anslist_,expr_,numfun_,FFvars_,reps_,hels_] := Module[{fulllist = Join[{expr},anslist],dots = Variables[{expr,anslist}],dotrules,ansnummat,nullspace},
dotrules = dotNumCompton[dots,numfun,FFvars,reps,hels];
ansnummat = ansNumerics[fulllist,dotrules];
nullspace = Map[toRational,NullSpace[ansnummat,Modulus->$P],{2}];
If[Length@nullspace==1,Drop[nullspace[[1]]/-nullspace[[1,1]],1] . anslist,"Null space contains more than one vector"]
];
(*use the functions (dotNumCompton,ansNumerics,ansIndep) to take in an ansatz list and do a partial reduction by checking pairwise linear dependence*)
ClearAll[pairindepFF];
pairindepFF[{},numfun_,FFvars_] := {};
pairindepFF[anslist_,numfun_,FFvars_,reps_] := Module[{dots = Variables[anslist],dotrules,ansnumvecs,ansnumindvecs},
dotrules = dotNumCompton[dots,numfun,FFvars,reps];
ansnumvecs = Thread[{Table[i,{i,Length@#}],#}]&@(Transpose[ansNumerics[anslist,dotrules]])(*numeric vectors with labelled entries*);
ansnumindvecs = DeleteDuplicates[DeleteCases[ansnumvecs,{_,Table[0,reps]}],MatrixRank[{#1[[2]],#2[[2]]},Modulus->$P]==1&](*independent vectors*);
anslist[[#]]&/@(#[[1]]&/@ansnumindvecs)(*independent analytic expressions*)
];


(* ::Text:: *)
(*Functions for generic kinematics*)


(*creates a set of numerics rules for individual dot products*)
ClearAll[dotNum];
dotNum[dots_,numfun_,FFvars_,massive_,massless_,reps_] := With[{normdots = dots//.Frule},
Thread[(dots/.{dot->d,pol->e,vec->pp,ap->nap,sp->nsp,momp->nmomp,spS->nS,spA->nA,F->nF,tFF->ntFF,ttFF->nttFF})->#]&/@
Map[toField,NumEvalMatrix[normdots,numfun,FFvars,massive,massless,reps],{2}]
];
(*similar to indepFF but separate 'dotNumCompton' out of it*)
ClearAll[indepFFeval];
indepFFeval[{},dotrules_] := {};
indepFFeval[anslist_,dotrules_] := Module[{ansnummat},
ansnummat = ansNumerics[anslist,dotrules];
ansIndep[anslist,ansnummat]
];


(* ::Chapter::Closed:: *)
(*Ansatz*)


(* ::Section::Closed:: *)
(*Compton Amplitude*)


(* ::Text:: *)
(*Below we define three functions:*)
(*1. ComptonAnsatz[dim,W] which returns all possible spinor structures of a given dimension dim, with Little group weights {w1,w2,w3,w4} (NB 1,2 massive; 3,4 massless)*)
(*2. SymmSelect[ansatz,symm] which selects the ansatz terms with given symmetries {symm((3<-->4)^star) ,  symm(1<-->2) } *)
(*3. BCFWbound[ansatz,zmax] which selects ansatz terms with scaling z^n, n <= zmax for z --> Infinity (under the shift {spS[3]->spS[3]+z spS[4],spA[4]->spA[4]-z spA[3]}).*)
(*Such functions are useful for the construction of an ansatz for arbitrary two-massive, two-massless Compton amplitudes.*)


(* ::Subsection::Closed:: *)
(*Ansatz Building Blocks*)


(* ::Text:: *)
(*Write all ansatz terms*)


terms = {ap[spA[3],spA[1]],ap[spA[3],spA[2]],ap[spA[4],spA[1]],ap[spA[4],spA[2]],
sp[spS[3],spS[1]],sp[spS[3],spS[2]],sp[spS[4],spS[1]],sp[spS[4],spS[2]],
ap[spA[3],spA[4]],sp[spS[3],spS[4]],
ap[spA[2],spA[1]],sp[spS[2],spS[1]],
momp[spS[4],vec[1],spA[3]],momp[spS[3],vec[1],spA[4]],
M^2,momp[spS[3],vec[1],spA[3]],momp[spS[4],vec[1],spA[4]]};
invterms = {M^2,momp[spS[3],vec[1],spA[3]],momp[spS[4],vec[1],spA[4]]};
equiv = {momp[spS[3],vec[2],spA[3]]->momp[spS[4],vec[1],spA[4]],momp[spS[4],vec[2],spA[4]]->momp[spS[3],vec[1],spA[3]],vec[4]->-vec[1]-vec[2]-vec[3],
momp[spS[3],vec[2],spA[4]]->-momp[spS[3],vec[1],spA[4]],momp[spS[4],vec[2],spA[3]]->-momp[spS[4],vec[1],spA[3]],m[1]->M,m[2]->M,m[3]->0,m[4]->0};
bcfwshift = {spS[3]->spS[3]+z spS[4],spA[4]->spA[4]-z spA[3]};


(* ::Text:: *)
(*Select all terms which include spinor 1 and spinor 2 (separately)*)


terms1 = Select[terms,(MemberQ[#,spA[1],Infinity]||MemberQ[#,spS[1],Infinity])&]
terms2 = Select[terms,(MemberQ[#,spA[2],Infinity]||MemberQ[#,spS[2],Infinity])&]


(* ::Text:: *)
(*Select all terms which include spinor 2 without spinor 1*)


terms2mod1 = Select[terms2,!(MemberQ[#,spA[1],Infinity]||MemberQ[#,spS[1],Infinity])&]


(* ::Text:: *)
(*Select all terms w/o 1 and 2, with nonzero weight in 3 and 4*)


leftover = Complement[Select[terms,!(MemberQ[#,spA[1],Infinity]||MemberQ[#,spS[1],Infinity]||MemberQ[#,spA[2],Infinity]||MemberQ[#,spS[2],Infinity])&],invterms]


(* ::Subsection::Closed:: *)
(*Ansatz Building Blocks (Covariant)*)


(* ::Text:: *)
(*Define gauge transformations*)


ClearAll[gaugeshift];
gaugeshift[i_] := pol[i]->pol[i]+ga[i] vec[i];


(* ::Text:: *)
(*Write all ansatz terms*)


covterms = {dot[pol[1],pol[2]],dot[pol[1],pol[3]],dot[pol[1],pol[4]],dot[pol[2],pol[3]],dot[pol[2],pol[4]],dot[pol[3],pol[4]],
dot[pol[1],vec[2]],dot[pol[1],vec[3]],dot[pol[2],vec[1]],dot[pol[2],vec[3]],dot[pol[3],vec[1]],dot[pol[3],vec[2]],dot[pol[4],vec[1]],dot[pol[4],vec[2]],
M^2,dot[vec[1],vec[3]],dot[vec[2],vec[3]]};
covinvterms = {M^2,dot[vec[1],vec[3]],dot[vec[2],vec[3]]};
covequiv = {dot[vec[1],vec[4]]->dot[vec[2],vec[3]],dot[vec[2],vec[4]]->dot[vec[1],vec[3]],dot[pol[x_],vec[4]]:>dot[pol[x],-vec[1]-vec[2]-vec[3]],dot[pol[4],vec[3]]->-dot[pol[4],vec[1]]-dot[pol[4],vec[2]],m[1]->M,m[2]->M,m[3]->0,m[4]->0};


(* ::Text:: *)
(*BCFW shift: NB need gauge dot[pol[3],pol[4]] = 0 if we want UNSHIFTED polarisation vectors*)


covbcfwshift = {vec[3]->vec[3]+z vec[R],vec[4]->vec[4]-z vec[R]};
covbcfwsimplify = {dot[vec[R],vec[R]]->0,dot[vec[R],vec[3]]->0,dot[vec[R],vec[4]]->0,dot[vec[R],vec[2]]->-dot[vec[R],vec[1]]};


(* ::Text:: *)
(*Select all terms which include pol1 and pol2 (separately)*)


covterms1 = Select[covterms,MemberQ[#,pol[1],Infinity]&]
covterms2 = Select[covterms,MemberQ[#,pol[2],Infinity]&]


(* ::Text:: *)
(*Select all terms which include spinor 2 without spinor 1*)


covterms2mod1 = Select[covterms2,!MemberQ[#,pol[1],Infinity]&]


(* ::Text:: *)
(*Select all terms w/o 1 and 2, with nonzero weight in 3 and 4, and terms with pol3 and pol4 separately*)


covleftover = Complement[Select[covterms,!(MemberQ[#,pol[1],Infinity]||MemberQ[#,pol[2],Infinity])&],covinvterms]
covleftover3 = Select[covleftover,!MemberQ[#,pol[4],Infinity]&]
covleftover4 = Select[covleftover,!MemberQ[#,pol[3],Infinity]&]


(* ::Text:: *)
(*Generalise covequiv to define a general basis reduction for a 4pt Compton amplitude*)
(*NB here {p1,p2} have mass M*)


ClearAll[basisred4];
basisred4[{{p1_,p2_},{p3_,p4_}},M_] :={
(*pol pol*)
dot[pol[x_],pol[x_]]:>0,
(*mom conserv*)
vec[p4]->-vec[p1]-vec[p2]-vec[p3],
(*pol vec*)
dot[pol[p4],vec[p3]]->-dot[pol[p4],vec[p1]]-dot[pol[p4],vec[p2]],
(*vec vec*)
dot[vec[p1],vec[p2]]->-dot[vec[p1],vec[p3]]-dot[vec[p2],vec[p3]]-M^2,
(*masses*)
m[p1]->M,m[p2]->M,m[p3]->0,m[p4]->0
}


(* ::Subsection::Closed:: *)
(*Ansatz Building Blocks (Covariant, Parity-Odd)*)


(* ::Text:: *)
(*Write down basis*)


(*parity even*)
eventerms = covterms/.M^2->M;
(*parity odd*)
oddterms = epsilon@@@DeleteDuplicates[Sort[{#[[1]],#[[2]],#[[3]],#[[4]]}]&/@Permutations[{vec[1],vec[2],vec[3],pol[1],pol[2],pol[3],pol[4]}]];
(*all terms*)
epsterms = Join[eventerms,oddterms]


(* ::Text:: *)
(*Write a general monomial*)


epsmonom = Times@@Power[epsterms,Table[n[i],{i,Length@epsterms}]]


(* ::Text:: *)
(*Compute useful quantities*)


(*find total mass dimension*)
epsdim = Plus@@Times[Length@Cases[{#},_vec|M,\[Infinity]]&/@epsterms,Table[n[i],{i,Length@epsterms}]]
(*find total weight for each leg*)
epsweights = Table[Plus@@Times[Length@Cases[{#},pol[i],\[Infinity]]&/@epsterms,Table[n[i],{i,Length@epsterms}]],{i,1,4}]


(* ::Subsection::Closed:: *)
(*Useful Functions*)


(* ::Text:: *)
(*Function to pick all monomials with a given weight in a given particle. Used to select the right weight for particle 1 at the start.*)
(*Also used in pickinv to select combination of (weight zero) terms with a given mass dimension.*)
(*And in covmissing.*)


pick[terms_List,W_Integer] := Module[{range = Length[terms],powers = {}},
powers = Flatten[Permutations/@(PadRight[#,range]&/@(Select[IntegerPartitions[W],(Length[#]<=range)&])),1];
(Times@@Power[terms,#]&)/@powers
];


(* ::Text:: *)
(*Function similar "pick", but to find all structures that, multiplied to an existing one, give the right weight for a given particle.*)
(*Iterated over all structures picked for particle 1, to multiply them by all structures that give the right weight for particle 2.*)


pickmod[terms_List,W_Integer,monom_List] :=Flatten[Times[#, pick[terms,W - Plus@@weights[#,2]]]&/@monom];


(* ::Text:: *)
(*Functions to take the list obtained by fixing the weights for 1 and 2, and remove terms that are not compatible with the overall weights, dimension etc (considering that we still need to fix 3 and 4)*)


weightfind[h3_Integer,h4_Integer,monom_List] := {#,h3-Subtract@@weights[#,3],h4-Subtract@@weights[#,4]}&/@monom;
evenbound[monom_List] := Select[monom,EvenQ[#[[2]]+#[[3]]]&];
dimpartialbound[dim_Integer,monom_List] := Select[monom,(massdim[#[[1]]]+Max[Abs@#[[2]],Abs@#[[3]]]<=dim)&];


(* ::Text:: *)
(*Functions to find, for each term found above, the factor that fixes the right weight in particles 3 and 4. Note that this is unique.*)
(*In addition another function that checks we do not exceed the required dimension at this step.*)


missing[hel3_Integer,hel4_Integer]/;EvenQ[hel3+hel4] := Which[
Abs[hel3] > Abs[hel4], If[hel3 > 0,momp[spS[3],vec[1],spA[4]]^((hel3-hel4)/2) sp[spS[3],spS[4]]^((hel3+hel4)/2),momp[spS[4],vec[1],spA[3]]^(-(hel3-hel4)/2) ap[spA[3],spA[4]]^(-(hel3+hel4)/2)],
Abs[hel3] <= Abs[hel4],If[hel4 > 0,momp[spS[4],vec[1],spA[3]]^((hel4-hel3)/2) sp[spS[3],spS[4]]^((hel4+hel3)/2),momp[spS[3],vec[1],spA[4]]^(-(hel4-hel3)/2) ap[spA[3],spA[4]]^(-(hel4+hel3)/2)]
];
masslessfix[monom_List] := Times[#[[1]],missing[#[[2]],#[[3]]]]&/@monom;
dimbound[dim_Integer,monom_List] := Select[monom,(massdim[#]<=dim)&];


(* ::Text:: *)
(*Function that adds all possible factors without any weight, ie {M,t13,t14}, in a way compatible with the required dimension.*)


pickinv[terms_List,dim_Integer,monom_List] :=Flatten[Times[#, pick[terms,(dim - massdim[#,{M}])/2]]&/@(If[EvenQ[dim-massdim[#]],#,M #]&/@monom)];


(* ::Text:: *)
(*Function that (anti)symmetrises all the monomials found, under the symmetries {(3<-->4)*,1<-->2}.*)


symmetrise[expr_,symm_List]/;(!(Head[expr]===List) && MemberQ[{{1,1},{1,-1},{-1,1},{-1,-1}},symm]) := 1/4 ((expr +#[[1]] swap[conjugate[expr],3,4])+#[[2]]swap[(expr +#[[1]]swap[conjugate[expr],3,4]),1,2])&@symm;


(* ::Subsection::Closed:: *)
(*Useful Functions (Covariant)*)


(* ::Text:: *)
(*Add a few other functions useful in the covariant case*)
(*Equivalent of pickmod*)


covpickmod[terms_List,W_Integer,monom_List] :=Flatten[Times[#, pick[terms,W - Plus@@covweights[#,2]]]&/@monom];


(* ::Text:: *)
(*Equivalent of weightfind (eliminating cases w too high weight on the yet-to-be-fixed massless particles)*)


covweightfind[h3_Integer,h4_Integer,monom_List] := Select[{#,h3-covweights[#,3],h4-covweights[#,4]}&/@monom,(#[[2]]>= 0 && #[[3]] >= 0)&];


(* ::Text:: *)
(*Equivalent of dimpartialbound, remove cases that we know will be too high mass dimensions once the massless polarisations are added*)


covdimbound[dim_Integer,monom_List] := Select[monom,(massdim[#[[1]]]+Abs[#[[2]]-#[[3]]]<=dim)&];


(* ::Text:: *)
(*Equivalent of missing, to find all possible structures with the right weights in pol3 and pol4*)


covmissing[dim_Integer,term_List] := With[{min = If[term[[2]]>=term[[3]],{term[[2]]-term[[3]],0},{0,term[[3]]-term[[2]]}]},Flatten@Table[term[[1]]dot[pol[3],pol[4]]^(Min[term[[2]],term[[3]]]-i) Flatten@Outer[Times,pick[covleftover3,min[[1]]+i], pick[covleftover4,min[[2]]+i]],{i,0,Min[1/2 (dim-(massdim[term[[1]]]+Abs[term[[2]]-term[[3]]])),term[[2]],term[[3]]]}]];


(* ::Text:: *)
(*Equivalent of masslessfix, to add to the ansatz terms all possible factors that fix the massless weights*)


covmasslessfix[dim_Integer,monom_List] := Flatten[covmissing[dim,#]&/@monom];


(* ::Subsection::Closed:: *)
(*Ansatz Functions*)


(* ::Text:: *)
(*First spinor-helicity functions*)


ComptonAnsatz[dim_Integer,W_List] := Module[{monom1={},monom12={},weightmonom12={},fixmonom12={},monom1234={}},
monom1 = pick[terms1,W[[1]]];
monom12 = pickmod[terms2mod1,W[[2]],monom1];
weightmonom12 = weightfind[W[[3]],W[[4]],monom12];
fixmonom12 = evenbound[dimpartialbound[dim,weightmonom12]];
monom1234 = dimbound[dim,masslessfix[fixmonom12]];
Return[pickinv[invterms,dim,monom1234]]
];

ComptonAnsatzAlt[dim_Integer,W_List] :=
pickinv[invterms,dim,
	dimbound[dim,
		masslessfix[
			evenbound[
				dimpartialbound[dim,
					weightfind[W[[3]],W[[4]],
						pickmod[terms2mod1,W[[2]],
							pick[terms1,W[[1]]]
						]
					]
				]
			]
		]
	]
];


SymmSelect[ansatz_List,symm_List]/; MemberQ[{{1,1},{1,-1},{-1,1},{-1,-1}},symm] := DeleteDuplicates[DeleteCases[Flatten[(symmetrise[#,symm]&/@ansatz)/.equiv],0],(#1===#2||#1===-#2)&];


BCFWbound[ansatz_List,zmax_Integer] := Select[ansatz,(Exponent[(#/.bcfwshift/.equiv),z]<= zmax)&];


BCFWlimit[expr_] := {Exponent[#,z],Coefficient[#,z,Exponent[#,z]]}&@(expr/.bcfwshift/.equiv);


(* ::Text:: *)
(*Then add some extra functions for covariant ansatz*)


ComptonAnsatzCov[dim_Integer,W_List] := Module[{monom1={},monom12={},weightmonom12={},fixmonom12={},monom1234={}},
monom1 = pick[covterms1,W[[1]]];
monom12 = covpickmod[covterms2mod1,W[[2]],monom1];
weightmonom12 = covweightfind[W[[3]],W[[4]],monom12];
fixmonom12 = covdimbound[dim,weightmonom12];
monom1234 = covmasslessfix[dim,fixmonom12];
Return[pickinv[covinvterms,dim,monom1234]]
];


SymmSelectCov[ansatz_List,symm_List]/; MemberQ[{{1,1},{1,-1},{-1,1},{-1,-1}},symm] := DeleteDuplicates[DeleteCases[Expand[Flatten[(symmetrise[#,symm]&/@ansatz)/.covequiv]],0],(#1===#2||#1===-#2)&];


BCFWboundCov[ansatz_List,zmax_Integer] := Select[ansatz,(Exponent[(#/.covbcfwshift/.covbcfwsimplify/.covequiv),z]<= zmax)&];


BCFWlimitCov[expr_] := {Exponent[#,z],Coefficient[#,z,Exponent[#,z]]}&@(expr/.covbcfwshift/.covbcfwsimplify/.covequiv);


(* ::Text:: *)
(*Finally parity-odd covariant ansatz*)


ClearAll[ComptonAnsatzEps];
ComptonAnsatzEps[dim_Integer,W_List] := Module[{Wcond={},Dcond={},TOTcond={}},
(*weight condition*)
Wcond = Thread[epsweights==W];
(*dimension condition*)
Dcond = {epsdim == dim};
(*together*)
TOTcond = Join[Wcond,Dcond,Table[n[i]>= 0,{i,Length@epsterms}]];
(*solve and find results*)(*NB can only have one (unresolved) power of epsilon*)
Select[epsmonom/.Solve[TOTcond,Integers],Length@Cases[{#},_epsilon,\[Infinity]]<2&]
];


(* ::Subsection::Closed:: *)
(*Ansatz Matching*)


(* ::Text:: *)
(*Define function to match ansatz to a given expression numerically*)


(*symbolic ansatz*)
ClearAll[NumAnsatzMatch];
NumAnsatzMatch[ansatz_,target_,fun_,vars_List,reps_Integer,hels_:{-1,1}] := Module[{equations = {},tempnum},
	Do[
		(*define temporary numerics*)
		tempnum = (#->random[dom])&/@vars;
		ga[3]=RandomInteger[max];ga[4]=RandomInteger[max];
		Numgen[fun[#,tempnum]&,{1,2},{{3,hels[[1]]},{4,hels[[2]]}}];
		(*equate ansatz and target and add to equation system*)(*NB remove gauge dependence ga[i] in covariant ansatz*)
		(*NB do not use Simplify w rational numerics since very slow*)
		Which[
		dom==0, AppendTo[equations,Quiet@Check[Chop[Simplify[(Numdict[ansatz,fun[#,tempnum]&,{1,2}] == Numdict[target,fun[#,tempnum]&,{1,2}])(*/.{ga[3]->RandomInteger[max],ga[4]->RandomInteger[max]}*)]],Nothing]];,
		dom==1, AppendTo[equations,Quiet@Check[(Numdict[ansatz,fun[#,tempnum]&,{1,2}] == Numdict[target,fun[#,tempnum]&,{1,2}])(*/.{ga[3]->RandomInteger[max],ga[4]->RandomInteger[max]}*),Nothing]];
		]
		(*reset numerics*)
		ClearAll[tempnum];
		ClearAll[ga];
		,{i,1,reps}
	];
	equations
]


(* ::Section::Closed:: *)
(*Five-Point Amplitude*)


(* ::Text:: *)
(*Below we give code to generate an ansatz for a four-massive-one-massless amplitude at arbitrary spin.*)
(*We work with covariant objects.*)
(*The steps are as follows:*)
(*1. define 5pt building blocks*)
(*2. make a function analogous to ComptonAnsatzCov above that builds up the ansatz in a way consistent with Little group and mass dimension. Note that we choose to think of trivalent Feynman diagrams, and we give maximum mass dimension determined by the pole structure of each diagram. The ansatz list will then be used for each diagram separately. *)


(* ::Subsection::Closed:: *)
(*Ansatz Building Blocks (Covariant)*)


(* ::Text:: *)
(*Define building blocks*)


polpol = dot[pol[#[[1]]],pol[#[[2]]]]&/@Subsets[Range[1,5],{2}]/.{5->k};
polvec = {
dot[pol[1],vec[2]],dot[pol[1],vec[3]],dot[pol[1],vec[4]],
dot[pol[2],vec[1]],dot[pol[2],vec[3]],dot[pol[2],vec[4]],
dot[pol[3],vec[1]],dot[pol[3],vec[2]],dot[pol[3],vec[4]],
dot[pol[4],vec[1]],dot[pol[4],vec[2]],dot[pol[4],vec[3]],
dot[pol[k],vec[1]],dot[pol[k],vec[2]],dot[pol[k],vec[3]]
};
vecvec = {T1k,T2k,dot[vec[1],vec[2]],S14,S23,M1^2,M2^2,M1 M2};
covterms5 = Join[Drop[Join[polpol,polvec,vecvec],-3],{M1,M2}];(*NB need to replace M_i M_j by M_i and M_j, better to use as a basis*)
covinvterms5 = vecvec;(*here instead it is important to have M_i M_j since we want dimension 2 only*)
covequiv5 = {
dot[pol[x_],vec[k]]:>dot[pol[x],-vec[1]-vec[2]-vec[3]-vec[4]],dot[pol[k],vec[4]]->dot[pol[k],-vec[1]-vec[2]-vec[3]],
dot[vec[1],vec[3]]->-(1/2)S14-dot[vec[1],vec[2]]-(1/2)T1k,dot[vec[2],vec[3]]->1/2 S23-M2^2,
dot[vec[2],vec[4]]->-(1/2)S23-dot[vec[1],vec[2]]-(1/2)T2k,dot[vec[1],vec[4]]->1/2 S14-M1^2,
dot[vec[3],vec[4]]->dot[vec[1],vec[2]]+(1/2)T1k+(1/2)T2k,
dot[vec[1],vec[k]]->(1/2)T1k,
dot[vec[2],vec[k]]->(1/2)T2k,
dot[vec[3],vec[k]]->(1/2)S14-(1/2)S23-(1/2)T2k,
dot[vec[4],vec[k]]->-(1/2)S14+(1/2)S23-(1/2)T1k,
T1q->-S14+S23-T1k,T2q->S14-S23-T2k,
m[1]->M1,m[2]->M2,m[3]->M2,m[4]->M1,m[k]->0,
dot[pol[x_],pol[x_]]:>0
};


(* ::Text:: *)
(*Select terms with a single weight in particle i and zero weights in particles 1, ..., i-1*)


covterms5o1 = Select[covterms5,MemberQ[#,pol[1],Infinity]&];
covterms5o21 = Select[covterms5,(MemberQ[#,pol[2],Infinity]&&!MemberQ[#,pol[1],Infinity])&];
covterms5o321 = Select[covterms5,(MemberQ[#,pol[3],Infinity]&&!MemberQ[#,pol[2],Infinity]&&!MemberQ[#,pol[1],Infinity])&];
covterms5o4321 = Select[covterms5,(MemberQ[#,pol[4],Infinity]&&!MemberQ[#,pol[3],Infinity]&&!MemberQ[#,pol[2],Infinity]&&!MemberQ[#,pol[1],Infinity])&];
covterms5ok4321 = Select[covterms5,(MemberQ[#,pol[k],Infinity]&&!MemberQ[#,pol[4],Infinity]&&!MemberQ[#,pol[3],Infinity]&&!MemberQ[#,pol[2],Infinity]&&!MemberQ[#,pol[1],Infinity])&];


(* ::Text:: *)
(*Generalise covequiv5 to define a general basis reduction for a 5pt amplitude with two massive lines and one massless leg*)
(*NB here {p1,p2} have mass M1 and {p3,p4} have mass M2*)


ClearAll[basisred5];
basisred5[{{p1_,p2_},{p3_,p4_},p5_},{M1_,M2_}] :={
(*pol pol*)
dot[pol[x_],pol[x_]]:>0,
(*pol vec*)
dot[pol[x_],vec[p5]]:>dot[pol[x],-vec[p1]-vec[p4]-vec[p3]-vec[p2]],
dot[pol[p5],vec[p2]]->-dot[pol[p5],vec[p1]]-dot[pol[p5],vec[p4]]-dot[pol[p5],vec[p3]],
(*vec vec*)
dot[vec[p1],vec[p3]]->-(dot[vec[p1],vec[p2]]+M1^2)-dot[vec[p1],vec[p5]]-dot[vec[p1],vec[p4]],
dot[vec[p4],vec[p2]]->-(dot[vec[p4],vec[p3]]+M2^2)-dot[vec[p4],vec[p5]]-dot[vec[p1],vec[p4]],
dot[vec[p3],vec[p2]]->dot[vec[p1],vec[p5]]+dot[vec[p4],vec[p5]]+dot[vec[p1],vec[p4]],
dot[vec[p3],vec[p5]]->(dot[vec[p1],vec[p2]]+M1^2)-(dot[vec[p4],vec[p3]]+M2^2)-dot[vec[p4],vec[p5]],dot[vec[p2],vec[p5]]->-(dot[vec[p1],vec[p2]]+M1^2)+(dot[vec[p4],vec[p3]]+M2^2)-dot[vec[p1],vec[p5]],dot[vec[p2],vec[p5]]->-(dot[vec[p1],vec[p2]]+M1^2)+(dot[vec[p4],vec[p3]]+M2^2)-dot[vec[p1],vec[p5]],dot[vec[p3],vec[p5]]->(dot[vec[p1],vec[p2]]+M1^2)-(dot[vec[p4],vec[p3]]+M2^2)-dot[vec[p4],vec[p5]],
(*masses*)
m[p1]->M1,m[p4]->M2,m[p3]->M2,m[p2]->M1,m[p5]->0
}


(* ::Subsection::Closed:: *)
(*Useful Functions*)


pickinv5[terms_List,dim_Integer,monom_List] :=Union[Flatten[Times[#, pick[terms,(dim - massdim[#,{M1,M2}])/2]]&/@Flatten[(If[EvenQ[dim-massdim[#]],#,Times[{M1,M2},#]]&/@monom)]]];


covpickmod5[terms_List,W_Integer,monom_List,i_] :=Flatten[Times[#, pick[terms,W - Plus@@covweights[#,i]]]&/@monom];


(* ::Subsection:: *)
(*Ansatz Functions*)


FivePtAnsatzCov[dim_Integer,W_List] := Module[{monom1={},monom21={},monom321={},monom4321={},monomk4321={}},
monom1 = pick[covterms5o1,W[[1]]];
monom21 = covpickmod5[covterms5o21,W[[2]],monom1,2];
monom321 = covpickmod5[covterms5o321,W[[3]],monom21,3];
monom4321 = covpickmod5[covterms5o4321,W[[4]],monom321,4];
monomk4321 = covpickmod5[covterms5ok4321,W[[5]],monom4321,k];
Return[pickinv5[covinvterms5,dim,monomk4321]]
];


(* ::Section::Closed:: *)
(*All-Point Ansatz*)


(* ::Text:: *)
(*Function to compute a covariant basis at arbitrary many points*)


ClearAll[BasisCovRel,BasisCov];
BasisCovRel[legs_Integer] := Join[Flatten[Table[Sum[dot[vec[i],vec[j]],{j,1,legs}]==0,{i,1,legs}]],Flatten[Table[Sum[dot[pol[i],vec[j]],{j,1,legs}]==0,{i,1,legs}]]];
BasisCovRel[leglist_List] := Join[Flatten[Table[Sum[dot[vec[i],vec[j]],{j,leglist}]==0,{i,leglist}]],Flatten[Table[Sum[dot[pol[i],vec[j]],{j,leglist}]==0,{i,leglist}]]];
BasisCov[legs_Integer,sols_List] := Join[Flatten@Table[dot[pol[i],pol[j]],{i,1,legs},{j,1,i-1}],Union@Cases[#[[2]]&/@sols,_dot|_m,\[Infinity]]];
BasisCov[leglist_List,sols_List] := Join[DeleteDuplicates@Flatten@Table[dot[pol[i],pol[j]],{i,leglist},{j,leglist}],Union@Cases[#[[2]]&/@sols,_dot|_m,\[Infinity]]];


(* ::Text:: *)
(*Function to compute a covariant ansatz at arbitrary many points*)
(*NB need to feed in a basis*)
(*NB this only contains dot products, no masses*)


ClearAll[AnsatzCov];
AnsatzCov[basis_List,weights_List,dim_Integer] := Module[{expbasis={},cond={},sols = {}},
(*create list w exponents*)
expbasis = Table[basis[[i]]^n[i],{i,1,Length@basis}];
(*weight conditions*)
Do[
AppendTo[cond,Plus@@(If[Union@Cases[#,pol[i],\[Infinity]]==={},0,#[[2]]]&/@expbasis)==weights[[i]]],
{i,1,Length@weights}];
(*dimension condition*)
AppendTo[cond, Plus@@(Length@Cases[#,_vec,\[Infinity]]#[[2]]&/@expbasis)==dim];
(*polynomial form condition*)
cond = Join[cond,Table[n[i]>=0,{i,Length@basis}]];
(*find solutions*)
sols = Solve[cond,Integers];
(*compute terms*)
If[Flatten@sols==={},{},Union[Times@@expbasis/.sols]]
]


(* ::Text:: *)
(*Function to give the FULL list of ansatz terms for a given dimension, including factors of the masses*)


ClearAll[AnsatzCovFull];
AnsatzCovFull[basis_List,weights_List,dim_Integer,masses_List] := Flatten@Table[Outer[Times,Union[Times@@@Tuples[masses,dim-i]],AnsatzCov[basis,weights,i]],{i,0,dim}];


(* ::Text:: *)
(*Alternative function:*)
(*(1) take as input a basis of dot products, a list of polarisations, a required little group weight and a required mass dimension*)
(*(2) generate lists of: all terms with pol[1], all terms with pol[2] without pol[1] etc, all terms without any pol*)
(*(3) pick all pox monomials from list with pol[1] with the correct little group weight (CAREFUL: dot[pol[1]] will have doubled weight)*)
(*(4) pick all pox monomials to "complete" the little group weight of pol[2]*)
(*(5) repeat for all pol[i]*)
(*(6) pick all monomials that complete the mass dimension*)


(*OLD: only works for {pol[1],pol[2]} due to covpickmod --> covweights[#,2] function only counting pol[2]*)
(*ClearAll[makeAnsatz];
makeAnsatz[basis_List,pols_List,weights_List,dim_Integer] /; Length@pols>1 := Module[{polterms = Table[Select[basis,(MemberQ[#,pols[[i]],Infinity]&&!MemberQ[#,Alternatives@@(pols[[1;;i-1]]),Infinity])&],{i,1,Length@pols}],momterms = Select[basis,!MemberQ[#,Alternatives@@pols,Infinity]&],allpols,ansatz},
allpols = DeleteCases[pick[polterms[[1]],weights[[1]]]/.Power[dot[_,_],Rational[_,_]]:>0,0];
Do[allpols = DeleteCases[covpickmod[polterms[[k]],weights[[k]],allpols]/.Power[dot[_,_],Rational[_,_]]:>0,0],{k,2,Length@pols}];
pickinv[momterms,dim,allpols]
];*)


ClearAll[makeAnsatz];
makeAnsatz[basis_List,pols_List,weights_List,dim_Integer] /; Length@pols>1 := Module[{polterms = Table[Select[basis,(MemberQ[#,pols[[i]],Infinity]&&!MemberQ[#,Alternatives@@(pols[[1;;i-1]]),Infinity])&],{i,1,Length@pols}],momterms = Select[basis,!MemberQ[#,Alternatives@@pols,Infinity]&],allpols,ansatz},
allpols = DeleteCases[pick[polterms[[1]],weights[[1]]]/.Power[dot[_,_],Rational[_,_]]:>0,0];
Do[allpols = DeleteCases[Flatten[(# pick[polterms[[k]],weights[[k]]-Plus@@Count[{decomp[#]},pols[[k]],\[Infinity]]]&)/@allpols]/.Power[dot[_,_],Rational[_,_]]:>0,0],{k,2,Length@pols}];
pickinv[momterms,dim,allpols]
];


(* ::Text:: *)
(*Function to make an ansatz using the 'makeAnsatz' function*)


(*function to make basis and basis reduction for ansatzfun*)
(*Example: basisfun[{Q1,Q2,Q3,Q4},{dot[vec[x_]]\[RuleDelayed]m[x]^2,dot[pol[x_]]\[RuleDelayed]0,dot[pol[x_],vec[x_]]\[RuleDelayed]0},{M,M,0,0}]*)
ClearAll[basisfun];
basisfun[legs_List,cond_,masses_] := Module[{tobasis,basis,massrule=Table[m[legs[[i]]]->masses[[i]],{i,Length@masses}]},
tobasis = Quiet@First@Solve[#,Union@Cases[#,_dot,\[Infinity]]]&@(BasisCovRel[legs]/.cond);
basis = DeleteCases[Union[BasisCov[legs,tobasis]/.cond/.{dot[pol[x_],pol[x_]]:>Sqrt[dot[pol[x],pol[x]]],m[x_]:>m[x]^2}/.massrule],0];
(*{basis,Join[cond,massrule,tobasis]}*){DeleteCases[basis//.#,0],#}&@Join[cond,massrule,tobasis]
]


(*"general" ansatz function, allowing for various powers of F and A*)
(*NB add an 'equirel' equivalence relation, to use additional relations (e.g. symmetry) when checking linear independence*)
(*Example: ansatzfun[{pol[Q1],pol[Q2],pol[Q3],pol[Q4]},{OSspin,OSspin,1,1},6,{1},offbasis4,tooffbasis4]/.c[x_]\[RuleDelayed]cE[x]*)
ClearAll[ansatzfun];
ansatzfun[pols_List,spins_List,mdim_,Fterms_List,basis_,tobasis_,equirel_:Identity] := Module[{anslist,ans,indepsol,coeffs},
anslist = Flatten[(# makeAnsatz[basis,pols,Table[spins[[i]]-countvar[Expand[#/.Frule],pols[[i]]],{i,Length@pols}],mdim-massdim[Expand[#/.Frule]]])&/@Fterms];
coeffs = Table[c[i],{i,Length@anslist}];
ans = Expand[Plus@@Times[coeffs,anslist]](*;
indepsol = If[ans===c[1],{},#->0&/@Complement[coeffs,Variables[#[[1]]&/@(Quiet@First@Solve@(setzero[#,Union@Cases[#,_dot|_m|M,\[Infinity]]]&@Expand[equirel[ans]/.Frule/.tobasis]))]]];
ans/.indepsol(*If[#===0,c[1],#]&@(ans/.indepsol)*)*)
]


(* ::Text:: *)
(*Function to give all Gram determinants consistent with the little group weights and mass dimension*)


ClearAll[gramDet];(*example:gramDet[{pol[Q1],pol[Q2],pol[Q3],pol[Q4],vec[Q1],vec[Q2],vec[Q3]},{w[Q1]\[Rule]2,w[Q2]\[Rule]2,w[Q3]\[Rule]1,w[Q4]\[Rule]1},4,4]*)
gramDet[vars_List,weightrules_List,mdim_Integer,dim_Integer:4] := Select[Flatten@Table[DeleteCases[Union[Flatten@Outer[Times,#,#]&@(epsilon@@@Subsets[vars,{ind}])/.pol[x_]:>\[Epsilon][x] pol[x]/.{\[Epsilon][x_]^n_/;n>(w[x]/.weightrules):>0}],0]/.\[Epsilon][x_]:>1,{ind,dim+1,Length@vars}],massdim[#]<=mdim&];


(* ::Text:: *)
(*Function to make an ansatz proportional to Gram determinants, using the 'gramDet' function*)


ClearAll[gramansatz];(*example:gramansatz[{pol[Q1],pol[Q2],pol[Q3],pol[Q4]},{2,2,1,1},{vec[Q1],vec[Q2],vec[Q3]},6,offbasis4,tooffbasis4]*)
gramansatz[pols_List,spins_List,vecs_List,mdim_Integer,basis_,tobasis_,equirel_:Identity,dim_Integer:4] := With[{weightrules=Thread[w@@@pols->spins],epsspins=Table[countvar[#,i],{i,pols}]&},DeleteCases[Union@Flatten[Times[#,Flatten[{ansatzfun[pols,spins-epsspins@#,mdim-massdim@#,{1},basis,tobasis,equirel]}/.Plus->List/.c[__]:>1](*OLD:List@@ansatzfun[pols,spins-epsspins@#,mdim-massdim@#,{1},basis,tobasis,equirel]/.c[__]\[RuleDelayed]1*)]&/@gramDet[Join[pols,vecs],weightrules,mdim,dim]],0]];


(* ::Text:: *)
(*Function to take an amplitude in terms of some (redundant) free parameters and return it in terms of non-redundant free parameters*)


(*ClearAll[reparametrise];
reparametrise[expr_,coeffs_:{c,g,gA}] := Module[{zerosol,zerocoeffs = #[__]:>0&/@coeffs},
	zerosol = First@Solve@setzero[Expand[(expr-(expr/.zerocoeffs))/.M\[Rule]1],_dot|M|_ap|_sp|_dp];
	Table[zerosol[[i,1]]->-l[i]+zerosol[[i,2]],{i,Length@zerosol}]
]*)
ClearAll[reparametrise];
reparametrise[expr_,coeffs_:{c,g,gA}] := Module[{zerosol,zerocoeffs = #[__]:>0&/@coeffs,coefflist=Union@Cases[expr,Alternatives@@(#[__]&/@coeffs),\[Infinity]]},
	zerosol = Quiet@First@Solve[setzero[Expand[M^1000 (expr-(expr/.zerocoeffs))(*/.M->1*)],_dot|M|_ap|_sp|_dp|_T|_trF|_trFF],coefflist];
	Table[zerosol[[i,1]]->-l[i]+zerosol[[i,2]],{i,Length@zerosol}]
]


(* ::Chapter::Closed:: *)
(*Graphs*)


(* ::Section::Closed:: *)
(*Graphs*)


(* ::Text:: *)
(*Function to draw a labelled graph*)
(*NOTATION (example): {{-1\[Phi][1]},{-2\[Phi][1]},{-3\[Phi][1]},{-4\[Phi][1]},{1\[Phi][1],5h,7\[Phi][1]},{4\[Phi][1],-7\[Phi][1],6h},{2\[Phi][1],8\[Phi][1],-5h},{3\[Phi][1],-6h,-8\[Phi][1]}}*)
(*--> box graph with two spin 1 massive lines and two exchanged gravitons*)
(*--> \[Phi][s] represents a particle of spin s*)
(*--> h represents graviton*)
(*--> multiplicative factor is the momentum*)
(*--> the first 4 entries are needed to draw the external lines*)
(*--> each curly bracket is a vertex*)


ClearAll[gPlot];
gPlot[graph_]:=With[{spi=(Union@Cases[graph,\[Phi][_],\[Infinity]][[1]])[[1]],mass=Select[Flatten[graph/.{\[Phi][_]:>1,h->0}],#>0&],nomass=Select[Flatten[graph/.{\[Phi][_]:>0,h->1}],#>0&]},GraphPlot[Join[Table[Labeled[Position[graph,Expand[i \[Phi][spi]],2][[1,1]]\[DirectedEdge]Position[graph,Expand[-i \[Phi][spi]],2][[1,1]],i \[Phi]],{i,mass}],Table[Labeled[Position[graph,Expand[i h]][[1,1]]\[DirectedEdge]Position[graph,Expand[-i h]][[1,1]],i h],{i,nomass}]],GraphLayout->"SpringEmbedding"]];


(*function to get canonical graphs BUT never permuting external vertices so the ext momenta stay distinct*)
ClearAll[canonicalIOnly,graphisoIOnly,fixLabelIOnly]
canonicalIOnly[edges_List] := Module[
  {
    eVerts, iVerts,                                          (* original vertex partitions                *)
    helpers,                                                 (* extra edges that \[OpenCurlyDoubleQuote]freeze\[CloseCurlyDoubleQuote] each e[\[Ellipsis]] label *)
    workG, canonG, iso,                                      (* graphs + one isomorphism                  *)
    iOrder, iRules                                           (* final renaming rule for i-vertices        *)
  },
  
  (* 0. collect vertex sets *)
  eVerts = DeleteDuplicates @ Cases[edges, _e, {2}];
  iVerts = DeleteDuplicates @ Cases[edges, _i, {2}];
  
  (* 1. attach  n leaf vertices to  e[n]  \[RightArrow]  each e-vertex now has a UNIQUE degree;
        this makes it impossible for any isomorphism to swap e-labels.            *)
  helpers = Flatten @ Table[
     UndirectedEdge[ex, Unique["aux$"]] & /@ Range[First[ex]],     (* First[e] is the integer n in e[n] *)
     {ex, eVerts}
  ];
  
  (* 2. build a simple auxiliary graph only for the canonicalisation step *)
  workG  = DeleteDuplicates@Join[Sort/@edges, helpers];
  canonG = EdgeList@CanonicalGraph@Graph[workG];
  
  (* 3. pick one isomorphism:  original \[RightArrow] canonical *)
  iso    = First @ FindGraphIsomorphism[workG, canonG];
  
  (* 4. sort i-vertices by where they landed, then map them to 1,2,\[Ellipsis]            *)
  iOrder = SortBy[iVerts, iso[#]&];
  iRules = Thread[iOrder -> Range[Length[iOrder]]];
  
  (* 5. apply the renaming ONLY to i-vertices; e-labels remain as-is *)
  Sort[edges /. iRules]
]
graphisoIOnly[edges_List] := Module[
  {
    eVerts, iVerts,                                          (* original vertex partitions                *)
    helpers,                                                 (* extra edges that \[OpenCurlyDoubleQuote]freeze\[CloseCurlyDoubleQuote] each e[\[Ellipsis]] label *)
    workG, canonG, iso,                                      (* graphs + one isomorphism                  *)
    iOrder, iRules                                           (* final renaming rule for i-vertices        *)
  },
  
  (* 0. collect vertex sets *)
  eVerts = DeleteDuplicates @ Cases[edges, _e, {2}];
  iVerts = DeleteDuplicates @ Cases[edges, _i, {2}];
  
  (* 1. attach  n leaf vertices to  e[n]  \[RightArrow]  each e-vertex now has a UNIQUE degree;
        this makes it impossible for any isomorphism to swap e-labels.            *)
  helpers = Flatten @ Table[
     UndirectedEdge[ex, Unique["aux$"]] & /@ Range[First[ex]],     (* First[e] is the integer n in e[n] *)
     {ex, eVerts}
  ];
  
  (* 2. build a simple auxiliary graph only for the canonicalisation step *)
  workG  = DeleteDuplicates@Join[Sort/@edges, helpers];
  canonG = EdgeList@CanonicalGraph@Graph[workG];
  
  (* 3. pick one isomorphism:  original \[RightArrow] canonical *)
  iso    = First @ FindGraphIsomorphism[workG, canonG];
  
  (* 4. sort i-vertices by where they landed, then map them to 1,2,\[Ellipsis]            *)
  iOrder = SortBy[iVerts, iso[#]&];
  iRules = Thread[iOrder -> Range[Length[iOrder]]];
  
  (* 5. return the relabelling rules, ie the graph isomorphism *)
  iRules
]
(*fixLabelIOnly[term_] := term/.(myGraphIsomorphism[Sort/@#,canonicalIOnly@(Sort/@#)]&@(getGraph[term]))[[1]];*)
fixLabelIOnly[term_] := term/.graphisoIOnly[getGraph[term]];


(*NEWER chatgpt version to handle mixed directed/undirected graphs*)
ClearAll[splitDuplicateEdges,graphisoIOnlyPorts,fixLabelIOnlyPorts];
(*first handle duplicate edges*)
splitDuplicateEdges[edges_List] := Module[
  {counts = Counts[edges], isDup, out, $mID = 0},
  isDup = AssociationThread[Keys@Select[counts, # >= 2 &] -> True];
  out = Reap[
    Do[
      With[{e = edges[[j]]},
        If[TrueQ[Lookup[isDup, e, False]],
          Module[{u, v, m = m[++$mID], h = Head[e]},
            {u, v} = List @@ e;
            Which[
              h === UndirectedEdge,
                (Sow[u \[UndirectedEdge] m]; Sow[m \[UndirectedEdge] v]),
              h === DirectedEdge,
                (Sow[u \[DirectedEdge] m]; Sow[m \[DirectedEdge] v]),
              True, Sow[e]
            ]
          ],
          Sow[e]
        ]
      ],
      {j, Length[edges]}
    ]
  ][[2, 1]];
  out
];
(*then find canonical labels*)
graphisoIOnlyPorts[Edges_List] := Module[
  {edges,eVerts, mVerts, iVerts, allVerts, hub, vin, vout, portWires, helpers, edgeGadgets,
   workEdges, workG, canonG, iso, iOrder, iRules},

  hub[v_] := h[v];  vin[v_] := pin[v];  vout[v_] := pout[v];
  
  edges = splitDuplicateEdges[Edges];

  eVerts  = DeleteDuplicates @ Cases[edges, _e, {2}];
  iVerts  = DeleteDuplicates @ Cases[edges, _i, {2}];
  mVerts = DeleteDuplicates @ Cases[edges,_m,{2}];
  allVerts = Join[eVerts, mVerts,iVerts];

  (* connect ports to hub + decorate ports: in=1 leaf, out=2 leaves *)
  portWires = Flatten @ Table[
     {
       UndirectedEdge[hub[v], vin[v]],
       UndirectedEdge[hub[v], vout[v]],
       UndirectedEdge[vin[v],  Unique["aux$in$"]],
       UndirectedEdge[vout[v], Unique["aux$out$"]],
       UndirectedEdge[vout[v], Unique["aux$out$"]]
     },
     {v, allVerts}
  ];

  (* freeze e[n] labels on the hub *)
  helpers = Flatten @ Table[
     UndirectedEdge[hub[ev], Unique["aux$e$"]] & /@ Range[First[ev]],
     {ev, eVerts}
  ];

  (* encode edges: undirected -> hub\[LongDash]hub; directed u->v -> u_out\[LongDash]v_in *)
  edgeGadgets = Replace[edges, {
      UndirectedEdge[u_, v_] :> UndirectedEdge[hub[u],  hub[v]],
      DirectedEdge[u_,   v_] :> UndirectedEdge[vout[u], vin[v]]
    }, {1}];

  workEdges = DeleteDuplicates @ Join[Sort /@ (portWires ~Join~ helpers ~Join~ edgeGadgets)];
  workG  = Graph[workEdges];
  canonG = CanonicalGraph[workG];
  iso    = First @ FindGraphIsomorphism[workG, canonG];

  iOrder = SortBy[iVerts, iso[hub[#]] &];
  iRules = Thread[iOrder -> Range[Length[iOrder]]];
  iRules
];
(*then implement function to use this*)
fixLabelIOnlyPorts[term_] := Sort[term/.graphisoIOnlyPorts[getGraphShow[term]]];
