(* ::Package:: *)

BeginPackage["GeneratorExample`"]
(**)

stredovyTvarV[m_,n_,r_] := ToString[TraditionalForm[(x-m)^2+(y-n)^2==HoldForm[r^2]], TeXForm];
stredovyTvarMM[m_,n_,r_] := (x-m)^2+(y-n)^2 == r^2;
diskriminantt[b_,a_,c_] :=ToString[HoldForm[b^2-4a "."c], TeXForm];
diskriminant[b_,a_,c_] :=ToString[HoldForm[Sqrt[b^2-4a "."c]], TeXForm];
(*kvadra[b_,d_,a_] := ToString[HoldForm[(-b \[PlusMinus]TraditionalForm[Sqrt[d]])/(2"."a)], TeXForm];*)
kvadra[b_,d_,a_,type_] := Module[{},
	If[type==1,
		Return[ToString[HoldForm[(-b +TraditionalForm[Sqrt[d]])/(2"."a)], TeXForm]];,
		Return[ToString[HoldForm[(-b -TraditionalForm[Sqrt[d]])/(2"."a)], TeXForm]];
	];
];
vseobecnyTvarM1[m_,n_,r_] := x^2 + y^2 -2m x -2n y + (m^2+n^2-r^2)== 0;
vzdialenostab[b1_,a1_,b2_,a2_,type_] := Module[{},
	If[type == 1,
		Return[ToString[HoldForm[Sqrt[( b1-a1)^2+( b2-a2)^2]], TeXForm]],
		Return[Sqrt[( b1-a1)^2+( b2-a2)^2]]
	];
];

Internal`$ContextMarks = False
Equation[difficulty_] := Module[{sx,sy,rr,solution,body,iks,svek,nvek,c,priamka,do},
	solution = {}; (*zadanie, postup, vysledok*)
	body = List[];
	
	While[Length[body]<3,
		body = List[];
		iks = List[];
		
		sx = RandomInteger[{-15,15}];
		sy = RandomInteger[{-15,15}];
		rr = RandomInteger[{2,10}];
		
		For[i=0, i<25, i++,
			xx = RandomInteger[{-15,15}];
			temp = SolveValues[(xx-sx)^2+(y-sy)^2 == rr^2,y];
			If[Element[temp[[1]],Integers] && !MemberQ[iks,xx],
				iks = Append[iks,xx];
				body = Append[body,{xx,temp[[1]]}];
				If[temp[[1]] != temp[[2]],
					body = Append[body,{xx,temp[[2]]}];
				];
			];
		];
	];
	
	svek = List[body[[3]][[1]]-body[[1]][[1]],body[[3]][[2]]-body[[1]][[2]]];
	nvek = List[-svek[[2]],svek[[1]]];
	c = -(body[[1]][[1]]*nvek[[1]])-(body[[1]][[2]]*nvek[[2]]);
	priamka = ToString[nvek[[1]]*x + nvek[[2]]*y + c == 0, TeXForm];
	do = SolveValues[nvek[[1]]*x + nvek[[2]]*y + c == 0,y][[1]];

	If[difficulty=="EASY",
		(*zadanie*)
		solution = Append[solution, "\\text{N\[AAcute]jdite priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}.};;;\\textit{k: }"];
		solution[[1]] = solution[[1]] <> stredovyTvarV[sx,sy,rr] <> ";;;\\textit{p: }" <> priamka <> ";;;;;;";
		
		(*postup*)
		solution = Append[solution, "\\text{Postup:};;;"];
		solution[[2]] = solution[[2]] <> "\\text{Zo zadanej priamky \\textit{p} vyjadr\[IAcute]me premenn\[UAcute] \\textit{y}.};;;";
		solution[[2]] = solution[[2]] <> priamka <> "\\rightarrow \\textit{y}=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadren\[UAcute] premenn\[UAcute] \\textit{y} dosad\[IAcute]me do rovnice kru\[ZHacek]nice \\textit{k} a rovnicu uprav\[IAcute]me.};;;";
		solution[[2]] = solution[[2]] <> ToString[TraditionalForm[SubtractSides[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> ToString[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{N\[AAcute]jdeme korene z\[IAcute]skanej kvadratickej rovnice.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vypo\[CHacek]\[IAcute]tame diskriminant pod\:013ea vzorca }D = b^2-4 a\\cdot c\\text{, kde }a,b,c\\in\\mathbb{R}\\text{ a s\[UAcute]};;;";
		solution[[2]] = solution[[2]] <> "\\text{koeficienty rovnice vo v\[SHacek]eobecnom tvare }ax^2+bx+c=0;;;";
		part = TraditionalForm[Expand[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]]]];
		
		(*Vypocet kvadratickej rovnice*)
		If[Length[part[[1]][[1]]] == 3,
			(*rovnica obsahuje 3 cleny*)
			If[Length[part[[1]][[1,2]]] != 0,
				(*ak b nie je 1*)
				dis = Sqrt[(part[[1]][[1,2,1]])^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[part[[1]][[1,2,1]],1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				(*ak b = 1*)
				dis = Sqrt[(1)^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[1,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[1,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[1,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[1,dis,1,2], "."->"\\cdot"] <> ";;;";
			],
			(*rovnica neobsahuje 3 cleny*)
			If[Length[part[[1]][[1,1]]] != 0,
				dis = Sqrt[(part[[1]][[1,1,1]])^2-4*1*0];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[part[[1]][[1,1,1]],1,0], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				dis = Sqrt[-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminant[0,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[0,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[0,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[0,dis,1,2], "."->"\\cdot"] <> ";;;";
			]
		];
		
		xka = SolveValues[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]],x];
		yyy = SolveValues[nvek[[1]]*x + nvek[[2]]*y + c == 0,y];
		
		solution[[2]] = solution[[2]] <> "x_1=" <> ToString[xka[[1]], TeXForm] <> ";;;x_2=" <> ToString[xka[[2]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadr\[IAcute]me }y_1\\text{, }y_2\\text{ ako y-ov\[EAcute] s\[UAcute]radnice priese\[CHacek]n\[IAcute]kov priamky \\textit{p} a kru\[ZHacek]nice \\textit{k}.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Do rovnice s vyjadrenou premennou \\textit{y} dosad\[IAcute]me }x_1\\text{, }x_2\\rightarrow y=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_1 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[1]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_2 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[2]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Z\[IAcute]skali sme priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}:};;;";
		solution[[2]] = solution[[2]] <> "\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[2]] = solution[[2]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;;;;";
		
		(*vysledok*)
		solution = Append[solution, "\\text{V\[YAcute]sledok:};;;"];
		solution[[3]] = solution[[3]] <> "\\text{Priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p} s\[UAcute]:};;;\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[3]] = solution[[3]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;";
		
		(*graficke riesenie*)
		a=StringJoin[{"A[",ToString[xka[[1]]],";",ToString[ReplaceAll[yyy,x->xka[[1]]][[1]]],"]"}];
		b=StringJoin[{"B[",ToString[xka[[2]]],";",ToString[ReplaceAll[yyy,x->xka[[2]]][[1]]],"]"}];
		str={Red,Style[Point[{sx,sy}],PointSize[0.015]],Style[Text[StringJoin[{"S[",ToString[sx],";",ToString[sy],"]"}],{sx,sy},{0,1.5}],Bold]};
		ba={Darker[Green],Style[Point[{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]}],PointSize[0.015]],Style[Text[a,{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]},{0,1.5}],Bold,Background->White]};
		bb={Darker[Green],Style[Point[{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]}],PointSize[0.015]],Style[Text[b,{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]},{0,1.5}],Bold,Background->White]};
		pr=Graphics[Plot[Re[y/. Solve[nvek[[1]]*x + nvek[[2]]*y + c == 0,y]],{x,xka[[1]]-3,xka[[2]]+3}]];
		
		img = Graphics[{Style[Circle[{sx,sy},rr],Black],str,ba,bb,First[pr]},Axes->True,AxesLabel->{"x","y"},ImageSize->Medium];
		solution[[3]] = solution[[3]] <> StringJoin["<image data:image/png;base64,",StringReplace[ExportString[img,{"Base64","PNG"}],"\n"->""],">"];
	];

	If[difficulty=="MEDIUM",
		(*zadanie*)
		solution = Append[solution, "\\text{N\[AAcute]jdite priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}.};;;\\textit{k: }"];
		solution[[1]] = solution[[1]] <> ToString[vseobecnyTvarM1[sx,sy,rr], TeXForm] <> ";;;\\textit{p: }" <> priamka <> ";;;;;;";
		
		(*postup*)
		solution = Append[solution, "\\text{Postup:};;;"];
		solution[[2]] = solution[[2]] <> "\\text{Zo zadanej priamky \\textit{p} vyjadr\[IAcute]me premenn\[UAcute] \\textit{y}.};;;";
		solution[[2]] = solution[[2]] <> priamka <> "\\rightarrow \\textit{y}=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadren\[UAcute] premenn\[UAcute] \\textit{y} dosad\[IAcute]me do rovnice kru\[ZHacek]nice \\textit{k} a rovnicu uprav\[IAcute]me.};;;";
		solution[[2]] = solution[[2]] <> ToString[TraditionalForm[SubtractSides[ReplaceAll[vseobecnyTvarM1[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> ToString[SubtractSides[Simplify[ReplaceAll[vseobecnyTvarM1[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{N\[AAcute]jdeme korene z\[IAcute]skanej kvadratickej rovnice.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vypo\[CHacek]\[IAcute]tame diskriminant pod\:013ea vzorca }D = b^2-4 a\\cdot c\\text{, kde }a,b,c\\in\\mathbb{R}\\text{ a s\[UAcute]};;;";
		solution[[2]] = solution[[2]] <> "\\text{koeficienty rovnice vo v\[SHacek]eobecnom tvare }ax^2+bx+c=0;;;";
		part = TraditionalForm[Expand[SubtractSides[Simplify[ReplaceAll[vseobecnyTvarM1[sx,sy,rr],y->do]]]]];
		
		(*Vypocet kvadratickej rovnice*)
		If[Length[part[[1]][[1]]] == 3,
			(*rovnica obsahuje 3 cleny*)
			If[Length[part[[1]][[1,2]]] != 0,
				(*ak b nie je 1*)
				dis = Sqrt[(part[[1]][[1,2,1]])^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[part[[1]][[1,2,1]],1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				(*ak b = 1*)
				dis = Sqrt[(1)^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "\\text{D = }" <> StringReplace[diskriminantt[1,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[1,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[1,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[1,dis,1,2], "."->"\\cdot"] <> ";;;";
			],
			(*rovnica neobsahuje 3 cleny*)
			If[Length[part[[1]][[1,1]]] != 0,
				dis = Sqrt[(part[[1]][[1,1,1]])^2-4*1*0];
				solution[[2]] = solution[[2]] <> "\\text{D = }" <> StringReplace[diskriminantt[part[[1]][[1,1,1]],1,0], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				dis = Sqrt[-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "\\text{D = }" <> StringReplace[diskriminant[0,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[0,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[0,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[0,dis,1,2], "."->"\\cdot"] <> ";;;";
			]
		];
		
		xka = SolveValues[SubtractSides[Simplify[ReplaceAll[vseobecnyTvarM1[sx,sy,rr],y->do]]],x];
		yyy = SolveValues[nvek[[1]]*x + nvek[[2]]*y + c == 0,y];
		
		solution[[2]] = solution[[2]] <> "x_1 = " <> ToString[xka[[1]], TeXForm] <> ";;;x_2 = " <> ToString[xka[[2]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadr\[IAcute]me }y_1\\text{, }y_2\\text{ ako y-ov\[EAcute] s\[UAcute]radnice priese\[CHacek]n\[IAcute]kov priamky \\textit{p} a kru\[ZHacek]nice \\textit{k}.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Do rovnice s vyjadrenou premennou \\textit{y} dosad\[IAcute]me }x_1\\text{, }x_2\\rightarrow y=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_1 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[1]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_2 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[2]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Z\[IAcute]skali sme priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}:};;;";
		solution[[2]] = solution[[2]] <> "\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[2]] = solution[[2]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;;;;";
		
		(*vysledok*)
		solution = Append[solution, "\\text{V\[YAcute]sledok:};;;"];
		solution[[3]] = solution[[3]] <> "\\text{Priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p} s\[UAcute]:};;;\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[3]] = solution[[3]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;";
		
		(*graficke riesenie*)
		a=StringJoin[{"A[",ToString[xka[[1]]],";",ToString[ReplaceAll[yyy,x->xka[[1]]][[1]]],"]"}];
		b=StringJoin[{"B[",ToString[xka[[2]]],";",ToString[ReplaceAll[yyy,x->xka[[2]]][[1]]],"]"}];
		str={Red,Style[Point[{sx,sy}],PointSize[0.015]],Style[Text[StringJoin[{"S[",ToString[sx],";",ToString[sy],"]"}],{sx,sy},{0,1.5}],Bold]};
		ba={Darker[Green],Style[Point[{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]}],PointSize[0.015]],Style[Text[a,{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]},{0,1.5}],Bold,Background->White]};
		bb={Darker[Green],Style[Point[{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]}],PointSize[0.015]],Style[Text[b,{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]},{0,1.5}],Bold,Background->White]};
		pr=Graphics[Plot[Re[y/. Solve[nvek[[1]]*x + nvek[[2]]*y + c == 0,y]],{x,xka[[1]]-3,xka[[2]]+3}]];
		
		img = Graphics[{Style[Circle[{sx,sy},rr],Black],str,ba,bb,First[pr]},Axes->True,AxesLabel->{"x","y"},ImageSize->Medium];
		solution[[3]] = solution[[3]] <> StringJoin["<image data:image/png;base64,",StringReplace[ExportString[img,{"Base64","PNG"}],"\n"->""],">"];
	];

	If[difficulty=="HARD",
		(*zadanie*)
		solution = Append[solution, "\\text{N\[AAcute]jdite priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}. Vypo\[CHacek]\[IAcute]tajte d\:013a\[ZHacek]ku vzniknutej tetivy \\textit{t}.};;;\\textit{k: }"];
		solution[[1]] = solution[[1]] <> stredovyTvarV[sx,sy,rr] <> ";;;\\textit{p: }" <> priamka <> ";;;;;;";
		
		(*postup*)
		solution = Append[solution, "\\text{Postup:};;;"];
		solution[[2]] = solution[[2]] <> "\\text{Zo zadanej priamky \\textit{p} vyjadr\[IAcute]me premenn\[UAcute] \\textit{y}.};;;";
		solution[[2]] = solution[[2]] <> priamka <> "\\rightarrow \\textit{y}=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadren\[UAcute] premenn\[UAcute] \\textit{y} dosad\[IAcute]me do rovnice kru\[ZHacek]nice \\textit{k} a rovnicu uprav\[IAcute]me.};;;";
		solution[[2]] = solution[[2]] <> ToString[TraditionalForm[SubtractSides[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> ToString[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{N\[AAcute]jdeme korene z\[IAcute]skanej kvadratickej rovnice.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vypo\[CHacek]\[IAcute]tame diskriminant pod\:013ea vzorca }D = b^2-4 a\\cdot c\\text{, kde }a,b,c\\in\\mathbb{R}\\text{ a s\[UAcute]};;;";
		solution[[2]] = solution[[2]] <> "\\text{koeficienty rovnice vo v\[SHacek]eobecnom tvare }ax^2+bx+c=0;;;";
		part = TraditionalForm[Expand[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]]]];
		
		(*Vypocet kvadratickej rovnice*)
		If[Length[part[[1]][[1]]] == 3,
			(*rovnica obsahuje 3 cleny*)
			If[Length[part[[1]][[1,2]]] != 0,
				(*ak b nie je 1*)
				dis = Sqrt[(part[[1]][[1,2,1]])^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[part[[1]][[1,2,1]],1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,2,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				(*ak b = 1*)
				dis = Sqrt[(1)^2-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[1,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[1,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[1,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[1,dis,1,2], "."->"\\cdot"] <> ";;;";
			],
			(*rovnica neobsahuje 3 cleny*)
			If[Length[part[[1]][[1,1]]] != 0,
				dis = Sqrt[(part[[1]][[1,1,1]])^2-4*1*0];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminantt[part[[1]][[1,1,1]],1,0], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1], "."->"\\cdot"] <> ";;;",*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[part[[1]][[1,1,1]],dis,1,2], "."->"\\cdot"] <> ";;;",
				
				dis = Sqrt[-4*1*part[[1]][[1,1]]];
				solution[[2]] = solution[[2]] <> "D=" <> StringReplace[diskriminant[0,1,part[[1]][[1,1]]], "."->"\\cdot"] <> "\\text{ = }"  <> ToString[dis, TeXForm] <> ";;;";
				solution[[2]] = solution[[2]] <> "\\text{Pre v\[YAcute]po\[CHacek]et kore\[NHacek]ov kvadratickej rovnice};;;\\text{pou\[ZHacek]ijeme vzorce }x_1=\\frac{-b+\\sqrt{D}}{2\\cdot a}\\text{ a }x_2=\\frac{-b-\\sqrt{D}}{2\\cdot a};;;";
				(*solution[[2]] = solution[[2]] <> "x_1\\text{, }x_2 = " <> StringReplace[kvadra[0,dis,1], "."->"\\cdot"] <> ";;;";*)
				solution[[2]] = solution[[2]] <> "x_1=" <> StringReplace[kvadra[0,dis,1,1], "."->"\\cdot"] <> ";;;";
				solution[[2]] = solution[[2]] <> "x_2=" <> StringReplace[kvadra[0,dis,1,2], "."->"\\cdot"] <> ";;;";
			]
		];
		
		xka = SolveValues[SubtractSides[Simplify[ReplaceAll[stredovyTvarMM[sx,sy,rr],y->do]]],x];
		yyy = SolveValues[nvek[[1]]*x + nvek[[2]]*y + c == 0,y];
		
		solution[[2]] = solution[[2]] <> "x_1 = " <> ToString[xka[[1]], TeXForm] <> ";;;x_2 = " <> ToString[xka[[2]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Vyjadr\[IAcute]me }y_1\\text{, }y_2\\text{ ako y-ov\[EAcute] s\[UAcute]radnice priese\[CHacek]n\[IAcute]kov priamky \\textit{p} a kru\[ZHacek]nice \\textit{k}.};;;";
		solution[[2]] = solution[[2]] <> "\\text{Do rovnice s vyjadrenou premennou \\textit{y} dosad\[IAcute]me }x_1\\text{, }x_2\\rightarrow y=" <> ToString[do, TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_1 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[1]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "y_2 = " <> ToString[TraditionalForm[ReplaceAll[yyy,x->TraditionalForm[ToString[xka[[2]]]]][[1]]], TeXForm] <> "\\text{ = }" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> ";;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{Z\[IAcute]skali sme priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p}:};;;";
		solution[[2]] = solution[[2]] <> "\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[2]] = solution[[2]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[2]] = solution[[2]] <> "\\text{\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_\\_};;;";
		solution[[2]] = solution[[2]] <> "\\text{D\:013a\[ZHacek]ku tetivy vypo\[CHacek]\[IAcute]tame ako vzdialenos\[THacek] bodov \\textit{A} a \\textit{B}};;;";
		solution[[2]] = solution[[2]] <> "\\text{Pou\[ZHacek]ijeme vzorec |AB| = }\\sqrt{(b_1-a_1)^2+(b_2-a_2)^2}\\text{, kde }a_1,a_2,b_1,b_2\\in\\mathbb{R}\\text{ a s\[UAcute] s\[UAcute]radnice bodov \\textit{A} a \\textit{B}};;;";
		
		If[xka[[1]]<0,
			kla = StringJoin[{"(",ToString[xka[[1]]],")"}],
			kla = xka[[1]]
		];
		If[ReplaceAll[yyy,x->xka[[1]]][[1]]<0,
			klb = StringJoin[{"(",ToString[ReplaceAll[yyy,x->xka[[1]]][[1]]],")"}],
			klb = ReplaceAll[yyy,x->xka[[1]]][[1]]
		];
		
		solution[[2]] = solution[[2]] <> "\\text{|AB| = }" <> vzdialenostab[xka[[2]],kla,ReplaceAll[yyy,x->xka[[2]]][[1]],klb,1] <> "\\text{ = }" <> ToString[Sqrt[( xka[[2]]-xka[[1]])^2+(ReplaceAll[yyy,x->xka[[1]]][[1]]-ReplaceAll[yyy,x->xka[[2]]][[1]])^2], TeXForm] <> ";;;;;;";
		
		(*vysledok*)
		solution = Append[solution, "\\text{V\[YAcute]sledok:};;;"];
		solution[[3]] = solution[[3]] <> "\\text{Priese\[CHacek]n\[IAcute]ky kru\[ZHacek]nice \\textit{k} a priamky \\textit{p} s\[UAcute]:};;;\\text{A[}" <> ToString[xka[[1]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[1]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[3]] = solution[[3]] <> "\\text{B[}" <> ToString[xka[[2]], TeXForm] <> "\\text{;}" <> ToString[ReplaceAll[yyy,x->xka[[2]]][[1]], TeXForm] <> "\\text{]};;;";
		solution[[3]] = solution[[3]] <> "\\text{D\:013a\[ZHacek]ka tetivy: |AB| = }" <> ToString[Sqrt[( xka[[2]]-xka[[1]])^2+(ReplaceAll[yyy,x->xka[[1]]][[1]]-ReplaceAll[yyy,x->xka[[2]]][[1]])^2], TeXForm] <> ";;;";
		
		(*graficke riesenie*)
		a=StringJoin[{"A[",ToString[xka[[1]]],";",ToString[ReplaceAll[yyy,x->xka[[1]]][[1]]],"]"}];
		b=StringJoin[{"B[",ToString[xka[[2]]],";",ToString[ReplaceAll[yyy,x->xka[[2]]][[1]]],"]"}];
		str={Red,Style[Point[{sx,sy}],PointSize[0.015]],Style[Text[StringJoin[{"S[",ToString[sx],";",ToString[sy],"]"}],{sx,sy},{0,1.5}],Bold]};
		ba={Darker[Green],Style[Point[{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]}],PointSize[0.015]],Style[Text[a,{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]},{0,1.5}],Bold,Background->White]};
		bb={Darker[Green],Style[Point[{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]}],PointSize[0.015]],Style[Text[b,{xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]},{0,1.5}],Bold,Background->White]};
		pr=Graphics[Plot[Re[y/. Solve[nvek[[1]]*x + nvek[[2]]*y + c == 0,y]],{x,xka[[1]]-3,xka[[2]]+3}]];
		tet = Line[{{xka[[1]],ReplaceAll[yyy,x->xka[[1]]][[1]]}, {xka[[2]],ReplaceAll[yyy,x->xka[[2]]][[1]]}}];
		
		img = Graphics[{Style[Circle[{sx,sy},rr],Black],str,ba,bb,First[pr],Style[tet,Red]},Axes->True,AxesLabel->{"x","y"},ImageSize->Medium];
		solution[[3]] = solution[[3]] <> StringJoin["<image data:image/png;base64,",StringReplace[ExportString[img,{"Base64","PNG"}],"\n"->""],">"];
	];

	Return[solution];
];

EndPackage[];
