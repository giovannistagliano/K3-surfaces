
///
installPackage "K3s";
-- check K3s
viewHelp (K3,ZZ,Nothing)
///

if version#"VERSION" < "1.18" then error "this package requires Macaulay2 version 1.18 or newer";

newPackage(
    "K3s",
    Version => "0.4", 
    Date => "September 15, 2021",
    Authors => {{Name => "Michael Hoff", 
                 Email => "hahn@math.uni-sb.de"},
                {Name => "Giovanni Staglianò", 
                 Email => "giovannistagliano@gmail.com"}},
    PackageExports => {"SpecialFanoFourfolds"},
    Keywords => {"Algebraic Geometry"},
    Headline => "Explicit constructions of K3 surfaces",
    DebuggingMode => false
)

if SpecialFanoFourfolds.Options.Version < "2.3" then (
    <<endl<<"Your version of the SpecialFanoFourfolds package is outdated (required version 2.3 or newer);"<<endl;
    <<"you can manually download the latest version from"<<endl;
    <<"https://github.com/Macaulay2/M2/tree/development/M2/Macaulay2/packages."<<endl;
    <<"To automatically download the latest version of SpecialFanoFourfolds in your current directory,"<<endl;
    <<"you may run the following Macaulay2 code:"<<endl<<"***"<<endl<<endl;
    <<///run "curl -s -o SpecialFanoFourfolds.m2 https://raw.githubusercontent.com/Macaulay2/M2/development/M2/Macaulay2/packages/SpecialFanoFourfolds.m2";///<<endl<<endl<<"***"<<endl;
    error "required SpecialFanoFourfolds package version 2.3 or newer";
);

export{"K3","K3surface","ideals","project","trigonalK3"}

debug SpecialFanoFourfolds;
needsPackage "Truncations";
needsPackage "MinimalPrimes";

t := local t;
ringPP = (n,K) -> Grass(0,n,K,Variable=>t);

K3surface = new Type of HashTable;

K3surface.synonym = "K3 surface";

GeneralK3surface = new Type of HashTable;

net K3surface := S -> (
    M := S#"lattice";
    d := M_(0,1);
    n := M_(1,1);
    g := lift((M_(0,0) + 2)/2,ZZ);
    w := "special K3 surface with rank 2 lattice defined by the intersection matrix: "|net(M);
    local g'; local c; local a; local b; local g0; local d0; local n0;
    w = w || concatenate for s in select(fewPossibilities,l -> take(l,{4,6}) == (g,d,n)) list ( 
    (g',c,a,b,g0,d0,n0) = s;
    "-- "|toString(a,b)|": K3 surface of degree "|toString(2*g'-2)|" and genus "|toString(g')|" containing "|(if n == 0 then "elliptic" else "rational")|" curve of degree "|toString(c)|" "|(if isAdmissible(2*g'-2) then "(cubic fourfold) " else "")|(if isAdmissibleGM(2*g'-2) then "(GM fourfold) " else "")|newline
    )
);

net GeneralK3surface := S -> (
    net("general K3 surface of genus "|toString(S#"genus")|" and degree "|toString(2*S#"genus"-2)|" in PP^"|toString(S#"genus"))
)

K3surface#{Standard,AfterPrint} = K3surface#{Standard,AfterNoPrint} = S -> (
    << endl << concatenate(interpreterDepth:"o") << lineNumber << " : " << "K3 surface" << endl;
);

GeneralK3surface#{Standard,AfterPrint} = GeneralK3surface#{Standard,AfterNoPrint} = S -> (
    << endl << concatenate(interpreterDepth:"o") << lineNumber << " : " << "K3 surface" << endl;
);

map (K3surface,ZZ,ZZ) := o -> (S,a,b) -> (S#"map") (a,b);

map GeneralK3surface := o -> S -> S#"map";

coefficientRing K3surface := S -> coefficientRing ring S#"surface";

coefficientRing GeneralK3surface := S -> coefficientRing map S;

genus (K3surface,ZZ,ZZ) := (S,a,b) -> (S#"genus") (a,b)

genus GeneralK3surface := S -> S#"genus";

degree (K3surface,ZZ,ZZ) := (S,a,b) -> 2 * genus(S,a,b) - 2;

degree GeneralK3surface := S -> 2 * genus(S) - 2;

K3surface Sequence := (S,ab) -> (
    if not(#ab == 2 and instance(first ab,ZZ) and instance(last ab,ZZ)) then error "expected a sequence of two integers";
    (a,b) := ab;
    f := map(S,a,b);
    I := if char coefficientRing S <= 65521 and genus(S,1,0) > 3 then image(f,"F4") else image f;
    if flatten degrees I != toList(binomial(genus(S,a,b)-2,2):2) then error "got wrong degrees for the generators";
    return I; 
);

ideal GeneralK3surface := S -> image map S;

ideals = method();

ideals K3surface := S -> (S#"curve",S#"surface");

ideals GeneralK3surface := S -> (S#"point",ideal S);

K3 = method(Options => {CoefficientRing => ZZ/65521, Verbose => true});

K3 ZZ := o -> (g) -> (
    K := o.CoefficientRing;
    local X; local p; local Ass;
    makegeneralK3 := (f,p,g) -> (
        new GeneralK3surface from {
            "map" => f,
            "point" => p,
            "genus" => g
        }
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) then (
        (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
        j := parametrize arandom({1},p);
        X = j^* X; p = j^* p;
        return makegeneralK3(rationalMap(quotient X,ring X),p,g);
    );
    if g == 11 then (
        if o.Verbose then <<"-- constructing general K3 surface of genus "<<g<<" and degree "<<2*g-2<<" in PP^"<<g<<endl;
        if o.Verbose then <<"-- (taking a random GM fourfold X of discriminant 20, hence containing a surface S of degree 9 and genus 2)"<<endl;
        X = specialGushelMukaiFourfold("surface of degree 9 and genus 2",K);
        if o.Verbose then <<"-- (running procedure 'associatedK3surface' for the GM fourfold X of discriminant 20)"<<endl<<"-- *** --"<<endl;
        Ass = associatedK3surface(X,Verbose=>o.Verbose);
        if o.Verbose then <<"-- *** --"<<endl;
        return makegeneralK3(last Ass,(last Ass) first Ass_2,g);
    );
    if g == 14 then (
        if o.Verbose then <<"-- constructing general K3 surface of genus "<<g<<" and degree "<<2*g-2<<" in PP^"<<g<<endl;
        error "procedure known but not implemented yet; see the function associatedK3surface from SpecialFanoFourfolds";
    );    
    if g == 20 then (
        if o.Verbose then <<"-- constructing general K3 surface of genus "<<g<<" and degree "<<2*g-2<<" in PP^"<<g<<endl;
        if o.Verbose then <<"-- (taking a random cubic fourfold X of discriminant 38, hence containing a surface S of degree 10 and genus 6)"<<endl;
        X = specialCubicFourfold("C38",K);
        if o.Verbose then <<"-- (running procedure 'associatedK3surface' for the cubic fourfold X of discriminant 38)"<<endl<<"-- *** --"<<endl;
        Ass = associatedK3surface(X,Verbose=>o.Verbose);
        if o.Verbose then <<"-- *** --"<<endl;
        return makegeneralK3(last Ass,(last Ass) first Ass_2,g);
    );
    if g == 22 then (
        if o.Verbose then <<"-- constructing general K3 surface of genus "<<g<<" and degree "<<2*g-2<<" in PP^"<<g<<endl;
        if o.Verbose then <<"-- (taking a random cubic fourfold X of discriminant 42, hence containing a surface S of degree 9 and genus 2)"<<endl;
        X = specialCubicFourfold("C42",K);
        if o.Verbose then <<"-- (running procedure 'associatedK3surface' for the cubic fourfold X of discriminant 42)"<<endl<<"-- *** --"<<endl;
        Ass = associatedK3surface(X,Verbose=>o.Verbose);
        if o.Verbose then <<"-- *** --"<<endl;
        return makegeneralK3(last Ass,(last Ass) first Ass_2,g);
    );
    error ("no procedure found to construct random K3 surface of genus "|(toString g));
);

K3 (ZZ,ZZ,ZZ) := o -> (g,d,n) -> (
    -- if o.Verbose then <<"-- constructing K3 surface with rank 2 lattice defined by the intersection matrix "<<matrix{{2*g-2,d},{d,n}}<<endl;   
    K := o.CoefficientRing;
    local X; local T; local C; local H; local p; local j;
    found := false;
    if g >= 3 and g <= 12 and d == 2 and n == -2 then (
        found = true;
        (T,C) = randomK3surfaceContainingConic(g,CoefficientRing=>K);
        H = if g != 10 and g != 12 then ideal first gens ring T else arandom({1},ring T);
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) and d == 1 and n == -2 then ( 
        found = true;
        (X,C) = randomMukaiThreefoldContainingLine(g,CoefficientRing=>K);
        j = parametrize arandom({1},C);
        (T,C) = (j^* X,j^* C);
        H = arandom({1},source j);
    );
    if (member(g,{3,4,5}) and d >= 3 and n == -2) and (g != 5 or d <= 8) and (g != 4 or d <= 6) and (g != 3 or d <= 8) then (
        found = true;
        C = randomRationalCurve(d,g,CoefficientRing=>K); 
        H = arandom({1},ringPP(g,K));
        T = arandom(if g == 3 then {4} else if g == 4 then {2,3} else {2,2,2},C);
    );
    if (member(g,{3,4,5}) and member(d,{3,4,5,6,7,8,9}) and n == 0) and (g != 5 or d <= 9) and (g != 4 or d <= 7) and (g != 3 or d <= 8) then (
        found = true;
        C = randomEllipticCurve(d,g,CoefficientRing=>K);
        H = arandom({1},ringPP(g,K));
        T = arandom(if g == 3 then {4} else if g == 4 then {2,3} else {2,2,2},C);
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) and d == 0 and n == -2 then (
        found = true;
        (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
        j = parametrize arandom({1},tangentSpace(X,p));
        T = j^* X; 
        C = j^* p; -- the node
    );
    if not found then error ("no procedure found to construct K3 surface with rank 2 lattice defined by the "|toString(matrix{{2*g-2,d},{d,n}}));
    g' := (a,b) -> lift((a^2*(2*g-2) + 2*a*b*d + b^2*n + 2)/2,ZZ);
    f := memoize(
        (a,b) -> (
            if d == 0 and n == -2 then if b != 0 then error "the source is a nodal K3 surface";
            phi := if b != 0 then mapDefinedByDivisor(quotient T,{(H,a),(C,b)}) else mapDefinedByDivisor(quotient T,{(H,a)});
            if numgens target phi =!= g'(a,b)+1 then error "something went wrong on the target of the map defined by the divisor";
            phi
        )
    );
    new K3surface from {
        "map" => f,
        "surface" => T,
        "curve" => C,
        "lattice" => matrix{{2*g-2,d},{d,n}},
        "genus" => g'
    }
);

trigonalK3 = method(Options => {CoefficientRing => ZZ/65521});
trigonalK3 ZZ := o -> g -> (
    -- See [Beauville - A remark on the generalized franchetta conjecture for K3 surfaces]
    if g < 8 then <<"--warning: expected g >= 8"<<endl; 
    n := (g-1)%3 + 1; if n == 1 then n = 4;
    a := lift((g-n)/3,ZZ); 
    assert(a > 0);
    K := o.CoefficientRing;
    P := PP_K^{1,n};
    S := if n == 2 then random({2,3},0_P) else 
         if n == 3 then random({{1,1},{1,3}},0_P) else 
         if n == 4 then random({{0,3},{1,1},{1,1}},0_P);
    f := rationalMap((0_P)%S,{a,1},Dominant=>true);
    assert(dim ambient target f == g and dim image f == 2 and degree image f == 2*g-2 and sectionalGenus image f == g);
    <<"-- got: "<<expression f<<endl;
    <<"-- degrees of image: "<<(concatenate for l in sort pairs tally flatten degrees ideal image f list (toString first l)|"^"|(toString(last l)|" "))<<"(expected degrees: 2^"<<binomial(g-2,2)<<")"<<endl;
    (multirationalMap first projections S,f)   
);

MAXa = 7;
MAXb = 7;

possible'a'b := (g,d,n) -> (
    local g'; local c;
    L := {};
    for a from 1 to MAXa do
        for b from 0 to MAXb do (
            g' = (a^2*(2*g-2) + 2*a*b*d + b^2*n + 2)/2;
            c = a*d + b*n;
            if floor g' == g' and g' >= g and c > 0 then L = append(L,(floor g',c,a,b));
        );
    L      
);
possibilities = {}
for g from 3 to 12 do for d from 1 to 15 do for n in {-2,0} do 
if (g >= 3 and g <= 12 and d == 2 and n == -2) or 
   (member(g,{3,4,5,6,7,8,9,10,12}) and d == 1 and n == -2) or 
   ((member(g,{3,4,5}) and d >= 3 and n == -2) and (g != 5 or d <= 8) and (g != 4 or d <= 6) and (g != 3 or d <= 8)) or 
   ((member(g,{3,4,5}) and member(d,{3,4,5,6,7,8,9}) and n == 0) and (g != 5 or d <= 9) and (g != 4 or d <= 7) and (g != 3 or d <= 8))
then possibilities = append(possibilities,(g,d,n));
possibilities = sort flatten for l in possibilities list apply(possible'a'b l,u -> append(append(append(u,l_0),l_1),l_2));
-- possibilities = {...,(g',c,a,b,g,d,n),...}
fewPossibilities = select(possibilities,l -> first l <= 51);

K3 (ZZ,Nothing) := o -> (G,nu) -> (
    P := select(possibilities,l -> first l == G);
    if #P == 0 then error "no procedure found";
    if o.Verbose then (
        local g'; local c; local a; local b; local g; local d; local n;
        for s in P do (
            (g',c,a,b,g,d,n) = s;
            <<"(K3("<<g<<","<<d<<","<<n<<"))("<<a<<","<<b<<") -- K3 surface of genus "<<g'<<" and degree "<<2*g'-2<<" containing "<<(if n == -2 then "rational" else if n == 0 then "elliptic" else "")<<" curve of degree "<<c<<endl;
        );
    );
    return apply(P,l -> take(l,{4,6}));
);

randomPointedMukaiThreefold = method(Options => {CoefficientRing => ZZ/65521});
randomPointedMukaiThreefold (ZZ) := o -> (g) -> (
    local p; local X; local j; local psi;
    K := o.CoefficientRing;
    if g == 3 then (
        p = point ringPP(4,K);
        X = arandom({4},p);
        return (X,p);
    );
    if g == 4 then (
        p = point ringPP(5,K);
        X = arandom({2,3},p);
        return (X,p);
    );
    if g == 5 then (
        p = point ringPP(6,K);
        X = arandom({2,2,2},p);
        return (X,p);
    );
    if g == 6 then (
        G14 := Grass(1,4,K,Variable=>t);
        p = trim lift(schubertCycle((3,3),G14),ambient G14);
        j = parametrize arandom({1,1},p);
        j = rationalMap(ringPP(7,K),source j) * j;
        X = j^* ideal G14;
        p = j^* p;
        X = trim(X + arandom(2,p));
        return (X,p);
    );
    if g == 7 then (
        quinticDelPezzoSurface := image rationalMap(ringPP(2,K),{3,4});
        psi = rationalMap(quinticDelPezzoSurface + arandom({1},ring quinticDelPezzoSurface),2);
        p = psi point source psi;
        j = parametrize arandom({1,1},p);
        j = rationalMap(ringPP(8,K),source j) * j;
        X = j^* image(2,psi);
        p = j^* p;
        return (X,p);
    );
    if g == 8 then (
        G15 := Grass(1,5,K,Variable=>t);
        p = trim lift(schubertCycle((4,4),G15),ambient G15);
        j = parametrize arandom({1,1,1,1,1},p);
        j = rationalMap(ringPP(9,K),source j) * j;
        X = j^* ideal G15;
        p = j^* p;
        return (X,p);
    );
    if g == 9 then (
        VeroneseSurfaceInP6 := trim(sub(kernel veronese(2,2,K,Variable=>(t,t)),ringPP(6,K)) + ideal last gens ringPP(6,K));
        psi = rationalMap(VeroneseSurfaceInP6,3,2);
        p = psi point source psi;
        j = parametrize arandom({1,1,1},p);
        j = rationalMap(ringPP(10,K),source j) * j;
        X = j^* image psi;
        p = j^* p;
        return (X,p);
    );
    if g == 10 then (
        XpLC10 := pointLineAndConicOnMukaiThreefoldOfGenus10(K,false,false);
        return (XpLC10_0,XpLC10_1);
    );
    if g == 12 then (
        XpLC12 := pointLineAndConicOnMukaiThreefoldOfGenus12(K,false,false);
        return (XpLC12_0,XpLC12_1);
    );
    error "the genus has to belong to the set {3,...,10,12}";
);

randomMukaiThreefoldContainingLine = method(Options => {CoefficientRing => ZZ/65521});
randomMukaiThreefoldContainingLine (ZZ) := o -> (g) -> (
    local L; local X; local j; local psi;
    K := o.CoefficientRing;
    if g == 3 then (
        L = arandom({1,1,1},ringPP(4,K));
        X = arandom({4},L);
        return (X,L);
    );
    if g == 4 then (
        L = arandom({1,1,1,1},ringPP(5,K));
        X = arandom({2,3},L);
        return (X,L);
    );
    if g == 5 then (
        L = arandom({1,1,1,1,1},ringPP(6,K));
        X = arandom({2,2,2},L);
        return (X,L);
    );
    if g == 6 then (
        G14 := Grass(1,4,K,Variable=>t);
        L = trim lift(schubertCycle((3,2),G14),ambient G14);
        j = parametrize arandom({1,1},L);
        j = rationalMap(ringPP(7,K),source j) * j;
        X = j^* ideal G14;
        L = j^* L;
        X = trim(X + arandom(2,L));
        return (X,L);
    );
    if g == 7 then (
        mapDP5 := rationalMap(ringPP(2,K),{3,4});
        quinticDelPezzoSurface := image mapDP5;
        pt := mapDP5 point ringPP(2,K);
        psi = rationalMap(quinticDelPezzoSurface + arandom({1},pt),2);
        L = psi ideal image basis(1,intersect(pt,point source psi));
        j = parametrize arandom({1,1},L);
        j = rationalMap(ringPP(8,K),source j) * j;
        X = j^* image(2,psi);
        L = j^* L;
        return (X,L);
    );
    if g == 8 then (
        G15 := Grass(1,5,K,Variable=>t);
        L = trim lift(schubertCycle((4,3),G15),ambient G15);
        j = parametrize arandom({1,1,1,1,1},L);
        j = rationalMap(ringPP(9,K),source j) * j;
        X = j^* ideal G15;
        L = j^* L;
        return (X,L);
    );
    if g == 9 then (
        mapVerInP6 := (rationalMap veronese(2,2,K,Variable=>(t,t))) * rationalMap(ringPP(5,K),ringPP(6,K),(vars ringPP(5,K))|matrix{{0_K}});
        VeroneseSurfaceInP6 := image mapVerInP6;
        psi = rationalMap(VeroneseSurfaceInP6,3,2);
        L = psi ideal image basis(1,intersect(mapVerInP6 point ringPP(2,K),point source psi));
        j = parametrize arandom({1,1,1},L);
        j = rationalMap(ringPP(10,K),source j) * j;
        X = j^* image psi;
        L = j^* L;
        return (X,L);
    );
    if g == 10 then (
        XpLC10 := pointLineAndConicOnMukaiThreefoldOfGenus10(K,true,false);
        return (XpLC10_0,XpLC10_2);
    );
    if g == 12 then (
        XpLC12 := pointLineAndConicOnMukaiThreefoldOfGenus12(K,true,false);
        return (XpLC12_0,XpLC12_2);
    );
    error "the genus has to belong to the set {3,...,10,12}";
);

randomK3surfaceContainingConic = method(Options => {CoefficientRing => ZZ/65521});
randomK3surfaceContainingConic (ZZ) := o -> (g) -> (
    if not (g >= 3 and g <= 12) then error "expected integer between 3 and 12";
    local X; local T; local C; local p; local j;
    K := o.CoefficientRing;    
    if member(g,{3,4,5,6,7,8,9,11}) then (
        (X,p) = randomPointedMukaiThreefold(g+1,CoefficientRing=>K);
        j = parametrize arandom({1},tangentSpace(X,p));
        T = j^* X;
        p = trim sub(j^* p,quotient j^* X);
        pr := rationalMap p; 
        (pr1,pr2) := graph pr;
        C = pr2 pr1^* p;
        T = image pr;
    );
    if g == 10 then (
        XpLC10 := pointLineAndConicOnMukaiThreefoldOfGenus10(K,false,true);
        (X,C) = (XpLC10_0,XpLC10_3);
        j = parametrize arandom({1},C);
        (T,C) = (j^* X,j^* C);
    );
    if g == 12 then (
        XpLC12 := pointLineAndConicOnMukaiThreefoldOfGenus12(K,false,true);
        (X,C) = (XpLC12_0,XpLC12_3);
        j = parametrize arandom({1},C);
        (T,C) = (j^* X,j^* C);
    );
    if not (dim C -1 == 1 and degree C == 2 and dim T -1 == 2 and degree T == 2*g-2 and isSubset(T,C)) then error "something went wrong";
    (T,C)
);

pointLineAndConicOnMukaiThreefoldOfGenus10 = (K,withLine,withConic) -> (
    line := null; conic := null;
    pts := apply(4,i -> point ringPP(2,K)); 
    p := point ringPP(2,K);
    f := rationalMap(sub(intersect pts,quotient arandom({5},intersect append(apply(pts,i -> i^2),p))),3);
    f = f * rationalMap(target f,ringPP(4,K),for i to 4 list random(1,target f));
    -- C is a curve of degree 7 and genus 2 in P^4 and p is one of its points 
    C := image f;
    p = f p;
    if not(dim C -1 == 1 and degree C == 7 and first genera C == 2 and dim p -1 == 0 and degree p == 1 and isSubset(C,p)) then error "something went wrong";
    -- Q is a quadric in P^4 containing C and a point q
    q := point ringPP(4,K);
    Q := quotient arandom({2},intersect(C,q));
    -- psi is the map Q --> PP^11 defined by the quintic hypersurfaces with double points along C
    psi := rationalMap(saturate (sub(C,Q))^2,5);
    if numgens target psi != 12 then error "something went wrong";
    if K === ZZ/(char K) then interpoleImage(psi,toList(28:2),2) else forceImage(psi,image(2,psi));
    X := psi#"idealImage";
    assert(X =!= null);
    q = psi q;
    if ? q != "one-point scheme in PP^11" then error "something went wrong";
    if withConic then (
        -- the base locus of psi is supported on C and a reducible curve D, the union of 4 lines
        D := saturate(trim lift(ideal matrix psi,ambient source psi),C);
        -- L is a line passing through p\in C which is contained in Q and intersects D in one point (thus psi L is a conic)
        -- (this needs to find a K-rational point on a certain 0-dimensional set defined over K)
        p' := select(decompose saturate(D + coneOfLines(ideal Q,p)),i -> dim i -1 == 0 and degree i == 1);
        if # p' == 0 then error ("failed to find conic on Mukai threefold of genus 10 defined over "|toString(K));
        L := ideal image basis(1,intersect(p,first p'));
        F := psi L;
        if not(dim F -1 == 1 and degree F == 2 and flatten degrees F == append(toList(9:1),2) and isSubset(X,F)) then error "something went wrong when trying to find conic on Mukai threefold of genus 10";
        conic = F;
    );
    if withLine then (
        psi = rationalMap(psi,Dominant=>true);
        -- B is the base locus of psi^-1, B-Supp(B) is a line.
        B := trim lift(ideal matrix approximateInverseMap(psi,Verbose=>false),ambient target psi);
        j := parametrize ideal matrix rationalMap(B,1);
        pr := rationalMap for i to 3 list random(1,source j);
        B' := pr j^* B;
        E' := B' : radical B';
        E := j radical trim (j^* X + pr^* E');
        if not(dim E -1 == 1 and degree E == 1 and flatten degrees E == toList(10:1) and isSubset(X,E)) then error "something went wrong when trying to find line on Mukai threefold of genus 10";
        line = E;
    );
    (X,q,line,conic)
);

pointLineAndConicOnMukaiThreefoldOfGenus12 = (K,withLine,withConic) -> (
    line := null; conic := null;
    f := rationalMap veronese(1,6,K,Variable=>(t,t));
    f = f * rationalMap(target f,ringPP(4,K),for i to 4 list random(1,target f));
    p := point ringPP(4,K);
    C := trim sub(image f,quotient arandom({2},intersect(p,image f)));
    psi := rationalMap(saturate(C^2),5);
    if numgens target psi != 14 then error "something went wrong";
    if K === ZZ/(char K) then interpoleImage(psi,toList(45:2),2) else forceImage(psi,image(2,psi));
    X := psi#"idealImage";
    assert(X =!= null);
    p = psi p;
    if ? p != "one-point scheme in PP^13" then error "something went wrong";
    if withConic then (
        psi = rationalMap(psi,Dominant=>true);
        -- B is the base locus of psi^-1, B-Supp(B) is a conic.
        B := trim lift(ideal matrix approximateInverseMap(psi,Verbose=>false),ambient target psi);
        j := parametrize ideal matrix rationalMap(B,1);
        pr := rationalMap for i to 3 list random(1,source j);
        B' := pr j^* B;
        E' := B' : radical B';
        E := j radical trim (j^* X + pr^* E');
        if not(dim E -1 == 1 and degree E == 2 and flatten degrees E == {1,1,1,1,1,1,1,1,1,1,1,2} and isSubset(X,E)) then error "something went wrong when trying to find conic on Mukai threefold of genus 12";
        conic = E;
    );
    if withLine then (
        C = trim lift(C,ringPP(4,K));
        q := f point source f;
        -- L is a secant line to the sextic curve C contained in the quadric, source of psi
        q' := select(decompose saturate(C + coneOfLines(ideal source psi,q),q),l -> dim l == 1 and degree l == 1);
        if # q' == 0 then error ("failed to find line on random Mukai threefold of genus 12 defined over "|toString(K));
        L := ideal image basis(1,intersect(q,first q'));
        F := psi L;
        if not(dim F -1 == 1 and degree F == 1 and flatten degrees F == toList(12:1) and isSubset(X,F)) then error "something went wrong when trying to find line on Mukai threefold of genus 12";
        line = F;
    );
    (X,p,line,conic)
);

------------------------------------------------------------
-- mukaiModel = method(Options => {CoefficientRing => ZZ/65521});
-- mukaiModel (ZZ) := o -> (g) -> (
--     K := o.CoefficientRing;
--     if not member(g,{6,7,8,9,10,12}) then error "expected the genus to be in the set {6,7,8,9,10,12}";
--     local psi;
--     if g == 6 then (
--         error "to be implemented";
--     );
--     if g == 7 then ( -- See [Zak - Tangents and secants of algebraic varieties - Thm. 3.8 (case 5), p. 67.]
--         G14inP10 := sub(sub(ideal Grass(1,4,K,Variable=>t),vars ringPP(9,K)),ringPP(10,K)) + (ideal last gens ringPP(10,K));
--         psi = rationalMap(G14inP10,2);
--         return (image psi,psi);
--     );
--     if g == 8 then (-- See [Zak - Tangents and secants of algebraic varieties - Thm. 3.8 (case 3), p. 67.]
--         P1xP3inP8 := minors(2,genericMatrix(ringPP(8,K),2,4)) + (ideal last gens ringPP(8,K));
--         psi = rationalMap(P1xP3inP8,2);
--         return (image psi,psi);
--     );
--     if g == 9 then ( -- I don't remember where I found this.
--         VeroneseSurfaceInP6 := minors(2,genericSymmetricMatrix(ringPP(6,K),3)) + (ideal last gens ringPP(6,K));
--         psi = rationalMap(VeroneseSurfaceInP6,3,2); 
--         return (image psi,psi);
--     );
--     if g == 10 or g == 12 then (
--         error "to be implemented";
--     );
-- );
------------------------------------------------------------

power0 := method();
power0 (Ideal,ZZ) := (p,d) -> (
   assert(isPolynomialRing ambient ring p and isHomogeneous ideal ring p and isHomogeneous p and unique degrees p == {{1}});
   if d <= 0 then error "expected a positive integer";
   L := trim sub(ideal random(1,ambient ring p),ring p);
   if d == 1 or d == 2 or d == 3 then return saturate(p^d,L);
   if d == 4 then return saturate((power0(p,2))^2,L);
   if d == 5 then return saturate(power0(p,2) * power0(p,3),L);
   if d == 6 then return saturate(power0(p,3) * power0(p,3),L);
   if d == 7 then return saturate(saturate(power0(p,3) * power0(p,2),L) * power0(p,2),L);
   if d == 8 then return saturate(power0(p,4) * power0(p,4),L);
   if d > 8 then error "not implemented yet";
);

project = method();
project (VisibleList,K3surface,ZZ,ZZ) := (L,S,a,b) -> (
   try assert(ring matrix{L} === ZZ and #L>0) else error "expected a list of integers";
   phi := map(S,a,b);
   d := max flatten degrees ideal matrix phi;
   J := rationalMap(intersect apply(L,i -> power0(point source phi,i)),d);   
   f := rationalMap(intersect(ideal matrix phi,ideal matrix J),d);
   if char coefficientRing S <= 65521 then image(f,"F4") else image f
);

tangentSpace (Ideal,Ideal) := (I,p) -> ideal tangentSpace(Var I,Var p);

randomEllipticNormalCurve = method(Options => {CoefficientRing => ZZ/65521});
randomEllipticNormalCurve (ZZ) := o -> (deg) -> (
    K := o.CoefficientRing;
    S := ringPP(2,K);
    y := gens S;
    E := y_2^2*y_0-y_1^3+random(0,S)*y_1*y_0^2+random(0,S)*y_0^3;
    n := deg -1;
    nO := saturate((ideal(y_0,y_1))^(n+1)+ideal E);
    d := max flatten degrees nO;
    Hs := gens nO;    
    H := Hs*random(source Hs,S^{-d});
    linsys1 := gens truncate(d,(ideal H +ideal E):nO);
    linsys := mingens ideal (linsys1 % ideal E);
    SE := S/E;          
    phi := map(SE,ringPP(n,K),sub(linsys,SE));
    trim kernel phi
);

randomEllipticCurve = method(Options => {CoefficientRing => ZZ/65521});
randomEllipticCurve (ZZ,ZZ) := o -> (d,n) -> (
    K := o.CoefficientRing;
    C := randomEllipticNormalCurve(d,CoefficientRing=>K);
    f := rationalMap(ringPP(d-1,K),ringPP(n,K),for i to n list random(1,ringPP(d-1,K)));
    f C
);

randomRationalNormalCurve = method(Options => {CoefficientRing => ZZ/65521});
randomRationalNormalCurve (ZZ) := o -> (deg) -> (
    K := o.CoefficientRing;
    trim kernel veronese(1,deg,K,Variable=>(t,t))
);

randomRationalCurve = method(Options => {CoefficientRing => ZZ/65521});
randomRationalCurve (ZZ,ZZ) := o -> (d,n) -> (
    K := o.CoefficientRing;
    C := randomRationalNormalCurve(d,CoefficientRing=>K);
    f := rationalMap(ringPP(d,K),ringPP(n,K),for i to n list random(1,ringPP(d,K)));
    f C
);


beginDocumentation() 

document {Key => K3s, 
Headline => "A package for constructing explicit examples of K3 surfaces"} 

document {Key => {K3surface}, 
Headline => "the class of all (polarized) K3 surfaces",
SeeAlso => {K3}}

document {Key => {K3,(K3,ZZ,ZZ,ZZ),[K3,Verbose],[K3,CoefficientRing]}, 
Headline => "make a special K3 surface",
Usage => "K3(d,g,n)
K3(d,g,n,CoefficientRing=>K)", 
Inputs => {"d" => ZZ,"g" => ZZ,"n" => ZZ}, 
Outputs => {{"a ",TO2{K3surface,"K3 surface"}," defined over ",TEX///$K$///," with rank 2 lattice defined by the intersection matrix ",TEX///$\begin{pmatrix} 2g-2 & d \\ d & n \end{pmatrix}$///}}, 
EXAMPLE {"time S = K3(6,1,-2)"},
SeeAlso => {(K3,ZZ),(K3,ZZ,Nothing)}}

document {Key => {(K3,ZZ,Nothing)}, 
Headline => "find function to construct K3 surface of given genus", 
Usage => "K3(G,)", 
Inputs => { ZZ => "G" => {"the genus"}}, 
Outputs => {List => {"a list of terns ",TT"(d,g,n)"," such that (",TO2{(K3,ZZ,ZZ,ZZ),TT"(K3(d,g,n)"},")",TO2{(symbol SPACE,K3surface,Sequence),"(a,b)"}," is the ideal of a K3 surface of genus ",TT"G",", for some integers ",TT"a,b"}}, 
EXAMPLE {"K3(11,)", "S = K3(5,5,-2)", "? S(1,2)", "? (map(S,1,2)) first ideals S"}, 
SeeAlso => {(K3,ZZ,ZZ,ZZ),(symbol SPACE,K3surface,Sequence)}} 

document {Key => {(K3,ZZ)}, 
Headline => "make a general K3 surface",
Usage => "K3 g
K3(g,CoefficientRing=>K)",
Inputs => {"g" => ZZ}, 
Outputs => {{"a general K3 surface defined over ",TEX///$K$///," of genus ",TEX///$g$///," in ",TEX///$\mathbb{P}^g$///}}, 
EXAMPLE {"time S = K3 9"},
SeeAlso => {(K3,ZZ,ZZ,ZZ)}}

document {Key => {(genus,K3surface,ZZ,ZZ)}, 
Headline => "genus of a K3 surface", 
Usage => "genus(S,a,b)", 
Inputs => {"S" => K3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {ZZ => {"the genus of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "genus(S,2,1)"}, 
SeeAlso => {(degree,K3surface,ZZ,ZZ)}} 

document {Key => {(degree,K3surface,ZZ,ZZ)}, 
Headline => "degree of a K3 surface", 
Usage => "degree(S,a,b)", 
Inputs => {"S" => K3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {ZZ => {"the degree of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "degree(S,2,1)"}, 
SeeAlso => {(genus,K3surface,ZZ,ZZ)}} 

document {Key => {project,(project,VisibleList,K3surface,ZZ,ZZ)}, 
Headline => "project a K3 surface", 
Usage => "project({i,j,k,...},S,a,b)", 
Inputs => {VisibleList => {"a list ",TEX///$\{i,j,k,\ldots\}$///," of nonnegative integers"},
           K3surface => "S" => {"a special K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///},
           ZZ => "a",
           ZZ => "b"}, 
Outputs => {Ideal => {"the ideal of the projection of ", TEX///$S$///,", embedded by the complete linear system ",TEX///$|a H + b C|$///,", from ",TEX///$i$///," random points of multiplicity 1, ",TEX///$j$///," random points of multiplicity 2, ",TEX///$k$///," random points of multiplicity 3, and so on until the last integer in the given list."}}, 
EXAMPLE {"time S = K3(8,2,-2)", "time P = project({5,3,1},S,2,1); -- (5th + 3rd + simple)-projection of S(2,1)","? P"}, 
SeeAlso => {(symbol SPACE,K3surface,Sequence)}} 

document {Key => {(coefficientRing,K3surface)}, 
Headline => "coefficient ring of a K3 surface", 
Usage => "coefficientRing S", 
Inputs => {"S" => K3surface}, 
Outputs => {Ring => {"the coefficient ring of ", TEX///$S$///}}, 
EXAMPLE {"K = ZZ/3331","S = K3(5,2,-2,CoefficientRing=>K)", "coefficientRing S"}} 

document {Key => {(symbol SPACE,K3surface,Sequence)}, 
Headline => "defining ideal of a K3 surface", 
Usage => "S(a,b)", 
Inputs => {"S" => K3surface => {"a special K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///},
          {{"a sequence of two integers ",TT"(a,b)"}}}, 
Outputs => {Ideal => {"the defining homogeneous ideal of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "time S(1,0)", "time S(2,1)"}, 
SeeAlso => {(map,K3surface,ZZ,ZZ),(ideals,K3surface)}} 

document {Key => {(map,K3surface,ZZ,ZZ)}, 
Headline => "defining map of a special K3 surface", 
Usage => "map S", 
Inputs => {"S" => K3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {{"the ",TO2{RationalMap,"birational morphism"}," defined by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(3,1,-2)", "f = map(S,2,1);", "isMorphism f", "degree f", "image f === S(2,1)"}, 
SeeAlso => {(symbol SPACE,K3surface,Sequence)}} 

undocumented {(net,K3surface)}

document {Key => {ideals,(ideals,K3surface)}, 
Headline => "corresponding ideals", 
Usage => "ideals S", 
Inputs => {"S" => K3surface => {"a special K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///}}, 
Outputs => {Ideal => {"the ideal of the special curve ",TEX///$C$///," contained in ",TEX///$S$///,", regarding ",TEX///$S$///," as embedded by ",TEX///$|H|$///},
            Ideal => {"the ideal of ",TEX///$S$///," as a surface embedded by ",TEX///$|H|$///}},
EXAMPLE {
"S = K3(5,2,-2)",
"(idC,idS) = ideals S",
"? idC",
"? idS"},
SeeAlso => {(symbol SPACE,K3surface,Sequence)}} 

-- Tests --

TEST /// -- randomPointedMukaiThreefold
debug K3s;
K = ZZ/333331;
for g in {3,4,5,6,7,8,9,10,12} do (
    <<"g = "<<g<<endl;
    time (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
    assert(isPolynomialRing ring X and coefficientRing ring X === K and numgens ring X == g+2);
    assert isSubset(X,p);
    assert (?p == "one-point scheme in PP^"|toString(g+1));
    assert(dim X -1 == 3);
    assert((genera X)_2 == g);
    assert(degree X == 2*g-2);
);
///

TEST /// -- randomMukaiThreefoldContainingLine
debug K3s;
K = ZZ/333331;
setRandomSeed 123456789
for g in {3,4,5,6,7,8,9,10,12} do (
    <<"g = "<<g<<endl;
    time (X,L) = randomMukaiThreefoldContainingLine(g,CoefficientRing=>K);
    assert(isPolynomialRing ring X and coefficientRing ring X === K and numgens ring X == g+2);
    assert isSubset(X,L);
    assert (?L == "line in PP^"|toString(g+1));
    assert(dim X -1 == 3);
    assert((genera X)_2 == g);
    assert(degree X == 2*g-2);
);
///

