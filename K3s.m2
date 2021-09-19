
if version#"VERSION" < "1.18" then error "this package requires Macaulay2 version 1.18 or newer";

newPackage(
    "K3s",
    Version => "0.6", 
    Date => "September 19, 2021",
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

export{"K3","LatticePolarizedK3surface","EmbeddedK3surface","project","mukaiModel","trigonalK3"}

debug SpecialFanoFourfolds;
needsPackage "Truncations";
needsPackage "MinimalPrimes";

LatticePolarizedK3surface = new Type of HashTable;

LatticePolarizedK3surface.synonym = "K3 surface";

EmbeddedK3surface = new Type of EmbeddedProjectiveVariety;

EmbeddedK3surface.synonym = "embedded K3 surface";

net LatticePolarizedK3surface := S -> (
    M := S#"lattice";
    d := M_(0,1);
    n := M_(1,1);
    g := lift((M_(0,0) + 2)/2,ZZ);
    w := "K3 surface with rank 2 lattice defined by the intersection matrix: "|net(M);
    local g'; local c; local a; local b; local g0; local d0; local n0;
    w = w || concatenate for s in select(fewPossibilities,l -> take(l,{4,6}) == (g,d,n)) list ( 
    (g',c,a,b,g0,d0,n0) = s;
    "-- "|toString(a,b)|": K3 surface of genus "|toString(g')|" and degree "|toString(2*g'-2)|" containing "|(if n == 0 then "elliptic" else "rational")|" curve of degree "|toString(c)|" "|(if isAdmissible(2*g'-2) then "(cubic fourfold) " else "")|(if isAdmissibleGM(2*g'-2) then "(GM fourfold) " else "")|newline
    )
);

? EmbeddedK3surface := S -> "K3 surface of genus "|toString(genus S)|" and degree "|toString(degree S)|" in PP^"|toString(dim ambient S);

LatticePolarizedK3surface#{Standard,AfterPrint} = LatticePolarizedK3surface#{Standard,AfterNoPrint} = S -> (
    << endl << concatenate(interpreterDepth:"o") << lineNumber << " : " << "Lattice-polarized K3 surface" << endl;
);

map (LatticePolarizedK3surface,ZZ,ZZ) := o -> (S,a,b) -> (
    if S.cache#?("map",a,b) then return S.cache#("map",a,b);
    M := S#"lattice";
    d := M_(0,1);
    n := M_(1,1);
    g := lift((M_(0,0) + 2)/2,ZZ);
    if d == 0 and n == -2 then if b != 0 then error "the source is a nodal K3 surface";
    H := ideal S.cache#"hyperplane";
    C := ideal S#"curve";
    phi := multirationalMap(if b != 0 then mapDefinedByDivisor(ring Var S,{(H,a),(C,b)}) else mapDefinedByDivisor(ring Var S,{(H,a)}));
    assert(source phi === Var S);
    if dim target phi =!= genus(S,a,b) then error "something went wrong on the target of the map defined by the divisor";
    S.cache#("map",a,b) = phi
);

map EmbeddedK3surface := o -> S -> S.cache#"mapK3";

coefficientRing LatticePolarizedK3surface := S -> coefficientRing S#"surface";

genus (LatticePolarizedK3surface,ZZ,ZZ) := (S,a,b) -> (
    M := S#"lattice";
    d := M_(0,1);
    n := M_(1,1);
    g := lift((M_(0,0) + 2)/2,ZZ);
    lift((a^2*(2*g-2) + 2*a*b*d + b^2*n + 2)/2,ZZ)
);

genus EmbeddedK3surface := S -> sectionalGenus S;

degree (LatticePolarizedK3surface,ZZ,ZZ) := (S,a,b) -> 2 * genus(S,a,b) - 2;

LatticePolarizedK3surface Sequence := (S,ab) -> (
    if not(#ab == 2 and instance(first ab,ZZ) and instance(last ab,ZZ)) then error "expected a sequence of two integers";
    (a,b) := ab;
    if S.cache#?("var",a,b) then return S.cache#("var",a,b);    
    f := map(S,a,b);
    if f#"image" === null and char coefficientRing S <= 65521 and genus(S,1,0) > 3 then f#"image" = Var image(toRationalMap f,"F4");
    -- if degrees image f =!= {({2},binomial(genus(S,a,b)-2,2))} then <<"--warning: the degrees for the generators are not as expected"<<endl;
    T := new EmbeddedK3surface from image f;
    f#"image" = T;
    T.cache#"mapK3" = f;
    S.cache#("var",a,b) = T
);

Var LatticePolarizedK3surface := o -> S -> S#"surface";

vars LatticePolarizedK3surface := S -> (S#"curve",Var S);

-- vars EmbeddedK3surface := S -> (S.cache#"pointK3",S);

K3 = method(Options => {CoefficientRing => ZZ/65521, Verbose => true});

K3 ZZ := o -> g -> (
    K := o.CoefficientRing;
    local X; local p; local Ass;
    makegeneralK3 := (f,p,g) -> (
        K3surf := new EmbeddedK3surface from image f;
        assert(sectionalGenus K3surf == g and degree K3surf == 2*g-2 and dim ambient K3surf == g and dim p == 0 and isSubset(p,K3surf));
        if g != 22 then assert(degree p == 1);
        f#"image" = K3surf;
        K3surf.cache#"mapK3" = f;
        K3surf.cache#"pointK3" = p;
        K3surf
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) then (
        (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
        j := parametrize random({1},p);
        X = j^* X; p = j^* p;
        return makegeneralK3(super 1_X,p,g);
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
        (T,C) = randomLatticePolarizedK3surfaceContainingConic(g,CoefficientRing=>K);
        H = if g != 10 and g != 12 then Var ideal first gens ring ambient T else random(1,0_T);
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) and d == 1 and n == -2 then ( 
        found = true;
        (X,C) = randomMukaiThreefoldContainingLine(g,CoefficientRing=>K);
        j = parametrize random({1},C);
        (T,C) = (j^* X,j^* C);
        H = random(1,0_T);
    );
    if (member(g,{3,4,5}) and d >= 3 and n == -2) and (g != 5 or d <= 8) and (g != 4 or d <= 6) and (g != 3 or d <= 8) then (
        found = true;
        C = randomRationalCurve(d,g,CoefficientRing=>K); 
        H = random(1,0_C);
        T = random(if g == 3 then {4} else if g == 4 then {{2},{3}} else {{2},{2},{2}},C);
    );
    if (member(g,{3,4,5}) and member(d,{3,4,5,6,7,8,9}) and n == 0) and (g != 5 or d <= 9) and (g != 4 or d <= 7) and (g != 3 or d <= 8) then (
        found = true;
        C = randomEllipticCurve(d,g,CoefficientRing=>K);
        H = random(1,0_C);
        T = random(if g == 3 then {4} else if g == 4 then {{2},{3}} else {{2},{2},{2}},C);
    );
    if member(g,{3,4,5,6,7,8,9,10,12}) and d == 0 and n == -2 then (
        found = true;
        (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
        j = parametrize random({1},tangentSpace(X,p));
        T = j^* X; 
        C = j^* p; -- the node
        H = random(1,0_T);
    );
    if not found then error ("no procedure found to construct K3 surface with rank 2 lattice defined by the "|toString(matrix{{2*g-2,d},{d,n}}));
    W := new CacheTable;
    W#"hyperplane" = H;
    new LatticePolarizedK3surface from {
        symbol cache => W,
        "surface" => T,
        "curve" => C,
        "lattice" => matrix{{2*g-2,d},{d,n}}
    }
);

trigonalK3 = method(TypicalValue => EmbeddedK3surface, Options => {CoefficientRing => ZZ/65521});
trigonalK3 ZZ := o -> g -> (
    -- See [Beauville - A remark on the generalized franchetta conjecture for K3 surfaces]
    if g < 5 then <<"--warning: expected g >= 5"<<endl; 
    n := (g-1)%3 + 1; if n == 1 then n = 4;
    a := lift((g-n)/3,ZZ); 
    assert(a > 0);
    K := o.CoefficientRing;
    P := PP_K^{1,n};
    S := if n == 2 then random({2,3},0_P) else 
         if n == 3 then random({{1,1},{1,3}},0_P) else 
         if n == 4 then random({{0,3},{1,1},{1,1}},0_P);
    f := rationalMap((0_P)%S,{a,1});
    T := new EmbeddedK3surface from image f;
    f#"image" = T;    
    assert(dim ambient target f == g and dim image f == 2 and degree image f == 2*g-2 and sectionalGenus image f == g);
    -- <<"-- got: "<<expression f<<endl;
    -- <<"-- degrees of image: "<<(concatenate for l in sort pairs tally flatten degrees ideal image f list (toString first l)|"^"|(toString(last l)|" "))<<"(expected degrees: 2^"<<binomial(g-2,2)<<")"<<endl;
    T.cache#"mapK3" = f;
    T
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
randomPointedMukaiThreefold ZZ := o -> g -> (
    local p; local X; local j; local psi;
    K := o.CoefficientRing;
    if g == 3 then (
        p = point PP_K^4;
        X = random({4},p);
        return (X,p);
    );
    if g == 4 then (
        p = point PP_K^5;
        X = random({{2},{3}},p);
        return (X,p);
    );
    if g == 5 then (
        p = point PP_K^6;
        X = random({{2},{2},{2}},p);
        return (X,p);
    );
    if g == 6 then (
        G14 := Var Grass(1,4,K,Variable=>"t");
        p = schubertCycle((3,3),G14);
        j = parametrize random({{1},{1}},p);
        p = j^* p;
        X = (j^* G14) * random(2,p);
        return (X,p);
    );
    if g == 7 then (
        quinticDelPezzoSurface := Var image rationalMap(ring PP_K^2,{3,4});
        psi = rationalMap(quinticDelPezzoSurface * random(1,0_quinticDelPezzoSurface),2);
        p = psi point source psi;
        j = parametrize random({{1},{1}},p);
        X = j^* Var image(2,toRationalMap psi);
        p = j^* p;
        return (X,p);
    );
    if g == 8 then (
        G15 := Var Grass(1,5,K,Variable=>"t");
        p = schubertCycle((4,4),G15);
        j = parametrize random({{1},{1},{1},{1},{1}},p);
        X = j^* G15;
        p = j^* p;
        return (X,p);
    );
    if g == 9 then (
        psi = rationalMap(image(PP_K^(2,2) << PP_K^6),3,2);
        p = psi point source psi;
        j = parametrize random({{1},{1},{1}},p);
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
randomMukaiThreefoldContainingLine ZZ := o -> g -> (
    local L; local X; local j; local psi;
    K := o.CoefficientRing;
    if g == 3 then (
        L = random({{1},{1},{1}},0_(PP_K^4));
        X = random({4},L);
        return (X,L);
    );
    if g == 4 then (
        L = random({{1},{1},{1},{1}},0_(PP_K^5));
        X = random({{2},{3}},L);
        return (X,L);
    );
    if g == 5 then (
        L = random({{1},{1},{1},{1},{1}},0_(PP_K^6));
        X = random({{2},{2},{2}},L);
        return (X,L);
    );
    if g == 6 then (
        G14 := Var Grass(1,4,K,Variable=>"t");
        L = schubertCycle((3,2),G14);
        j = parametrize random({{1},{1}},L);
        L = j^* L;
        X = (j^* G14) * random(2,L);
        return (X,L);
    );
    if g == 7 then (
        mapDP5 := multirationalMap rationalMap(ring PP_K^2,{3,4});
        pt := mapDP5 point source mapDP5;
        psi = rationalMap((image mapDP5) * random(1,pt),2);
        L = psi linearSpan {pt,point source psi};
        j = parametrize random({{1},{1}},L);
        X = j^* Var image(2,toRationalMap psi);
        L = j^* L;
        return (X,L);
    );
    if g == 8 then (
        G15 := Var Grass(1,5,K,Variable=>"t");
        L = schubertCycle((4,3),G15);
        j = parametrize random({{1},{1},{1},{1},{1}},L);
        X = j^* G15;
        L = j^* L;
        return (X,L);
    );
    if g == 9 then (
        mapVerInP6 := (parametrize PP_K^(2,2)) << PP_K^6;
        psi = rationalMap(image mapVerInP6,3,2);
        L = psi linearSpan {mapVerInP6 point source mapVerInP6,point source psi};
        j = parametrize random({{1},{1},{1}},L);
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

randomLatticePolarizedK3surfaceContainingConic = method(Options => {CoefficientRing => ZZ/65521});
randomLatticePolarizedK3surfaceContainingConic ZZ := o -> g -> (
    if not (g >= 3 and g <= 12) then error "expected integer between 3 and 12";
    local X; local T; local C; local p; local j;
    K := o.CoefficientRing;    
    if member(g,{3,4,5,6,7,8,9,11}) then (
        (X,p) = randomPointedMukaiThreefold(g+1,CoefficientRing=>K);
        j = parametrize random({1},tangentSpace(X,p));
        T = j^* X;
        p = (j^* p) % T;
        pr := rationalMap p; 
        (pr1,pr2) := graph pr;
        C = pr2 pr1^* p;
        T = image pr;
    );
    if g == 10 then (
        XpLC10 := pointLineAndConicOnMukaiThreefoldOfGenus10(K,false,true);
        (X,C) = (XpLC10_0,XpLC10_3);
        j = parametrize random({1},C);
        (T,C) = (j^* X,j^* C);
    );
    if g == 12 then (
        XpLC12 := pointLineAndConicOnMukaiThreefoldOfGenus12(K,false,true);
        (X,C) = (XpLC12_0,XpLC12_3);
        j = parametrize random({1},C);
        (T,C) = (j^* X,j^* C);
    );
    if not (dim C == 1 and degree C == 2 and sectionalGenus C == 0 and dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and isSubset(C,T)) then error "something went wrong";
    (T,C)
);

pointLineAndConicOnMukaiThreefoldOfGenus10 = (K,withLine,withConic) -> (
    line := null; conic := null;
    pts := apply(4,i -> point PP_K^2); 
    p := point PP_K^2;
    f := rationalMap((⋃ pts) % random(5,p + ⋃ apply(pts,i -> 2*i)),3);
    f = f * rationalMap point target f;
    -- C is a curve of degree 7 and genus 2 in P^4 and p is one of its points 
    C := image f;
    p = f p;
    if not(dim C == 1 and degree C == 7 and sectionalGenus C == 2 and dim p == 0 and degree p == 1 and isSubset(p,C)) then error "something went wrong";
    -- Q is a quadric in P^4 containing C and a point q
    q := point target f;
    Q := random(2,C + q);
    -- psi is the map Q --> PP^11 defined by the quintic hypersurfaces with double points along C
    psi := rationalMap(C_Q,5,2);
    if dim target psi != 11 then error "something went wrong";
    psi = toRationalMap psi;
    if K === ZZ/(char K) then interpoleImage(psi,toList(28:2),2) else forceImage(psi,image(2,psi));
    psi = multirationalMap psi;
    X := psi#"image";
    assert(X =!= null);
    q = psi q;
    if ? ideal q != "one-point scheme in PP^11" then error "something went wrong";
    if withConic then (
        -- the base locus of psi is supported on C and a reducible curve D, the union of 4 lines
        D := (Var trim lift(ideal matrix toRationalMap psi,ring ambient source psi)) \\ C;
        -- L is a line passing through p\in C which is contained in Q and intersects D in one point (thus psi L is a conic)
        -- (this needs to find a K-rational point on a certain 0-dimensional set defined over K)
        p' := select(decompose(D * coneOfLines(Q,p)),i -> dim i == 0 and degree i == 1);
        if # p' == 0 then error ("failed to find conic on Mukai threefold of genus 10 defined over "|toString(K));
        L := linearSpan {p,first p'};
        F := psi L;
        if not(dim F == 1 and degree F == 2 and flatten degrees ideal F == append(toList(9:1),2) and isSubset(F,X)) then error "something went wrong when trying to find conic on Mukai threefold of genus 10";
        conic = F;
    );
    if withLine then (
        psi = toRationalMap rationalMap(psi,Dominant=>true);
        -- B is the base locus of psi^-1, B-Supp(B) is a line.
        B := trim lift(ideal matrix approximateInverseMap(psi,Verbose=>false),ambient target psi);
        j := parametrize ideal matrix rationalMap(B,1);
        pr := rationalMap for i to 3 list random(1,source j);
        B' := pr j^* B;
        E' := B' : radical B';
        E := j radical trim (j^* ideal X + pr^* E');
        if not(dim E -1 == 1 and degree E == 1 and flatten degrees E == toList(10:1) and isSubset(ideal X,E)) then error "something went wrong when trying to find line on Mukai threefold of genus 10";
        line = Var E;
    );
    (X,q,line,conic)
);

pointLineAndConicOnMukaiThreefoldOfGenus12 = (K,withLine,withConic) -> (
    line := null; conic := null;
    f := rationalMap veronese(1,6,K);
    f = f * rationalMap(target f,ring PP_K^4,for i to 4 list random(1,target f));
    p := ideal point PP_K^4;
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
        C = trim lift(C,ring PP_K^4);
        q := f point source f;
        -- L is a secant line to the sextic curve C contained in the quadric, source of psi
        q' := select(decompose saturate(C + coneOfLines(ideal source psi,q),q),l -> dim l == 1 and degree l == 1);
        if # q' == 0 then error ("failed to find line on random Mukai threefold of genus 12 defined over "|toString(K));
        L := ideal image basis(1,intersect(q,first q'));
        F := psi L;
        if not(dim F -1 == 1 and degree F == 1 and flatten degrees F == toList(12:1) and isSubset(X,F)) then error "something went wrong when trying to find line on Mukai threefold of genus 12";
        line = F;
    );
    (Var X,Var p,if line === null then line else Var line,if conic === null then conic else Var conic)
);

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
project (VisibleList,LatticePolarizedK3surface,ZZ,ZZ) := (L,S,a,b) -> (
   try assert(ring matrix{L} === ZZ and #L>0) else error "expected a list of integers";
   E := invProjection(L,degree(S,a,b),genus(S,a,b),genus(S,a,b));
   phi := toRationalMap map(S,a,b);
   d := max flatten degrees ideal matrix phi;
   J := rationalMap(intersect apply(L,i -> power0(point source phi,i)),d);   
   f := rationalMap(intersect(ideal matrix phi,ideal matrix J),d);
   X := if char coefficientRing S <= 65521 then Var image(f,"F4") else Var image f;
   <<endl;
   if E != (degree X,sectionalGenus X,dim ambient X) then <<"--warning: output is not as expected"<<endl else <<"-- (degree and genus are as expected)"<<endl;
   X
);

invProjection = method();
invProjection (VisibleList,ZZ,ZZ,ZZ) := (mm,d,g,N) -> (
   expNumHyp := (d0,g0,r0,J) -> (
       t := local t;
       R := QQ[t];
       hP := (d,g) -> (1/2)*d*t^2 + ((1/2)*d+1-g)*t+2;
       max(binomial(r0+J,J) - sub(hP(d0,g0),t=>J),0)
   );
   mm = deepSplice mm; 
   <<"-- *** simulation ***"<<endl;
   <<"-- surface of degree "<<d<<" and sectional genus "<<g<<" in PP^"<<N<<" (quadrics: "<<expNumHyp(d,g,N,2)<<", cubics: "<<expNumHyp(d,g,N,3)<<")"<<endl;
   for m in mm do (
       (d,g,N) = (d - m^2,g - binomial(m,2),N - binomial(m+1,2)); 
       <<"-- surface of degree "<<d<<" and sectional genus "<<g<<" in PP^"<<N<<" (quadrics: "<<expNumHyp(d,g,N,2)<<", cubics: "<<expNumHyp(d,g,N,3)<<")"<<endl;
   );
   (d,g,N)
);

randomEllipticNormalCurve = method(Options => {CoefficientRing => ZZ/65521});
randomEllipticNormalCurve ZZ := o -> deg -> (
    K := o.CoefficientRing;
    S := ring PP_K^2;
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
    phi := map(SE,ring PP_K^n,sub(linsys,SE));
    Var trim kernel phi
);

randomEllipticCurve = method(Options => {CoefficientRing => ZZ/65521});
randomEllipticCurve (ZZ,ZZ) := o -> (d,n) -> (
    K := o.CoefficientRing;
    C := randomEllipticNormalCurve(d,CoefficientRing=>K);
    f := rationalMap(ring PP_K^(d-1),ring PP_K^n,for i to n list random(1,ring PP_K^(d-1)));
    f C
);

randomRationalCurve = method(Options => {CoefficientRing => ZZ/65521});
randomRationalCurve (ZZ,ZZ) := o -> (d,n) -> (
    K := o.CoefficientRing;
    C := PP_K^(1,d);
    f := rationalMap(ring ambient C,ring PP_K^n,for i to n list random(1,ring ambient C));
    f C
);

mukaiModel = method(Options => {CoefficientRing => ZZ/65521});
mukaiModel ZZ := o -> g -> (
    K := o.CoefficientRing;
    if not member(g,{6,7,8,9,10,12}) then error "expected the genus to be in the set {6,7,8,9,10,12}";
    local psi; local X;
    if g == 6 then (
        psi = rationalMap(image(Var sub(ideal(PP_K[1,1,1]),ring PP_K^6) << PP_K^7),2,Dominant=>true);
        X = image psi;
        X.cache#"rationalParametrization" = psi;
        assert(dim X == 7 and codim X == 3 and degree X == 5 and sectionalGenus X == 1);
        return X;
    );
    if g == 7 then ( -- See [Zak - Tangents and secants of algebraic varieties - Thm. 3.8 (case 5), p. 67.]
        psi = rationalMap(image(Var Grass(1,4,K,Variable=>"t") << PP_K^10),2,Dominant=>true);
        X = image psi;
        X.cache#"rationalParametrization" = psi;
        assert(dim X == 10 and codim X == 5 and degree X == 12 and sectionalGenus X == 7);
        return X;
    );
    if g == 8 then (-- See [Zak - Tangents and secants of algebraic varieties - Thm. 3.8 (case 3), p. 67.]
        psi = rationalMap(image(PP_K[1,1,1,1] << PP_K^8),2,Dominant=>true);
        X = image psi;
        X.cache#"rationalParametrization" = psi;
        assert(dim X == 8 and codim X == 6 and degree X == 14 and sectionalGenus X == 8);
        return X;
    );
    if g == 9 then (
        psi = rationalMap(image(PP_K^(2,2) << PP_K^6),3,2,Dominant=>true);
        X = image psi;
        X.cache#"rationalParametrization" = psi;
        assert(dim X == 6 and codim X == 7 and degree X == 16 and sectionalGenus X == 9);
        return X;
    );
    if g == 10 then ( -- p. 4 of [Kapustka and Ranestad - Vector Bundles On Fano Varieties Of Genus Ten] 
        w := gens ring PP_K^13;
        M := matrix {{0,-w_5,w_4,w_6,w_7,w_8,w_0},
                     {w_5,0,-w_3,w_12,w_13,w_9,w_1},
                     {-w_4,w_3,0,w_10,w_11,-w_6-w_13,w_2},
                     {-w_6,-w_12,-w_10,0,w_2,-w_1,w_3},
                     {-w_7,-w_13,-w_11,-w_2,0,w_0,w_4},
                     {-w_8,-w_9,w_6+w_13,w_1,-w_0,0,w_5},
                     {-w_0,-w_1,-w_2,-w_3,-w_4,-w_5,0}};
        X = projectiveVariety pfaffians(4,M);
        assert(dim X == 5 and codim X == 8 and degree X == 18 and sectionalGenus X == 10);
        return X;
    );
    if g == 12 then ( -- see also pointLineAndConicOnMukaiThreefoldOfGenus12
        C := PP_K^(1,6);
        C = (rationalMap linearSpan{point ambient C,point ambient C}) C;
        psi = rationalMap(C_(random(2,C)),5,2,Dominant=>2);
        psi#"isDominant" = true;
        X = target psi;
        X.cache#"rationalParametrization" = psi;
        assert(dim X == 3 and codim X == 10 and degree X == 22 and sectionalGenus X == 12);
        return X;
    );
);


beginDocumentation() 

document {Key => K3s, 
Headline => "A package for constructing explicit examples of K3 surfaces"} 

document {Key => {LatticePolarizedK3surface}, 
Headline => "the class of all lattice-polarized K3 surfaces",
SeeAlso => {K3,EmbeddedK3surface}}

document {Key => {EmbeddedK3surface}, 
Headline => "the class of all embedded K3 surfaces",
SeeAlso => {LatticePolarizedK3surface,(symbol SPACE,LatticePolarizedK3surface,Sequence)}}

document {Key => {K3,(K3,ZZ,ZZ,ZZ),[K3,Verbose],[K3,CoefficientRing]}, 
Headline => "make a lattice-polarized K3 surface",
Usage => "K3(d,g,n)
K3(d,g,n,CoefficientRing=>K)", 
Inputs => {"d" => ZZ,"g" => ZZ,"n" => ZZ}, 
Outputs => {{"a ",TO2{LatticePolarizedK3surface,"K3 surface"}," defined over ",TEX///$K$///," with rank 2 lattice defined by the intersection matrix ",TEX///$\begin{pmatrix} 2g-2 & d \\ d & n \end{pmatrix}$///}}, 
EXAMPLE {"K3(6,1,-2)"},
SeeAlso => {(K3,ZZ),(K3,ZZ,Nothing),(symbol SPACE,LatticePolarizedK3surface,Sequence)}}

document {Key => {(K3,ZZ,Nothing)}, 
Headline => "find function to construct K3 surface of given genus", 
Usage => "K3(G,)", 
Inputs => { ZZ => "G" => {"the genus"}}, 
Outputs => {List => {"a list of terns ",TT"(d,g,n)"," such that (",TO2{(K3,ZZ,ZZ,ZZ),TT"(K3(d,g,n)"},")",TO2{(symbol SPACE,LatticePolarizedK3surface,Sequence),"(a,b)"}," is a K3 surface of genus ",TT"G",", for some integers ",TT"a,b"}}, 
EXAMPLE {"K3(11,)", "S = K3(5,5,-2)", "S(1,2)", "(map(S,1,2)) first vars S"}, 
SeeAlso => {(K3,ZZ,ZZ,ZZ),(symbol SPACE,LatticePolarizedK3surface,Sequence)}} 

document {Key => {(K3,ZZ)}, 
Headline => "make a general K3 surface",
Usage => "K3 g
K3(g,CoefficientRing=>K)",
Inputs => {"g" => ZZ}, 
Outputs => {EmbeddedK3surface => {"a general K3 surface defined over ",TEX///$K$///," of genus ",TEX///$g$///," in ",TEX///$\mathbb{P}^g$///}}, 
EXAMPLE {"K3 9"},
SeeAlso => {(K3,ZZ,ZZ,ZZ)}}

document {Key => {(genus,LatticePolarizedK3surface,ZZ,ZZ)}, 
Headline => "genus of a K3 surface", 
Usage => "genus(S,a,b)", 
Inputs => {"S" => LatticePolarizedK3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {ZZ => {"the genus of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "genus(S,2,1)"}, 
SeeAlso => {(degree,LatticePolarizedK3surface,ZZ,ZZ)}} 

document {Key => {(degree,LatticePolarizedK3surface,ZZ,ZZ)}, 
Headline => "degree of a K3 surface", 
Usage => "degree(S,a,b)", 
Inputs => {"S" => LatticePolarizedK3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {ZZ => {"the degree of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "degree(S,2,1)"}, 
SeeAlso => {(genus,LatticePolarizedK3surface,ZZ,ZZ)}} 

document {Key => {project,(project,VisibleList,LatticePolarizedK3surface,ZZ,ZZ)}, 
Headline => "project a K3 surface", 
Usage => "project({i,j,k,...},S,a,b)", 
Inputs => {VisibleList => {"a list ",TEX///$\{i,j,k,\ldots\}$///," of nonnegative integers"},
           LatticePolarizedK3surface => "S" => {"a lattice-polarized K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///},
           ZZ => "a",
           ZZ => "b"}, 
Outputs => {EmbeddedProjectiveVariety => {"the projection of ", TEX///$S$///," embedded by the complete linear system ",TEX///$|a H + b C|$///," from ",TEX///$i$///," random points of multiplicity 1, ",TEX///$j$///," random points of multiplicity 2, ",TEX///$k$///," random points of multiplicity 3, and so on until the last integer in the given list."}}, 
EXAMPLE {"S = K3(8,2,-2)", "project({5,3,1},S,2,1); -- (5th + 3rd + simple)-projection of S(2,1)"}, 
SeeAlso => {(symbol SPACE,LatticePolarizedK3surface,Sequence)}} 

document {Key => {(coefficientRing,LatticePolarizedK3surface)}, 
Headline => "coefficient ring of a K3 surface", 
Usage => "coefficientRing S", 
Inputs => {"S" => LatticePolarizedK3surface}, 
Outputs => {Ring => {"the coefficient ring of ", TEX///$S$///}}, 
EXAMPLE {"K = ZZ/3331","S = K3(5,2,-2,CoefficientRing=>K)", "coefficientRing S"}} 

document {Key => {(symbol SPACE,LatticePolarizedK3surface,Sequence)}, 
Headline => "image of the embedding of a K3 surface", 
Usage => "S(a,b)", 
Inputs => {"S" => LatticePolarizedK3surface => {"a lattice-polarized K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///},
          {{"a sequence of two integers ",TT"(a,b)"}}}, 
Outputs => {EmbeddedK3surface => {"the image of the embedding of ", TEX///$S$///," by the complete linear system ",TEX///$|a H + b C|$///}}, 
EXAMPLE {"S = K3(5,2,-2)", "S(1,0)", "S(2,1)"}, 
SeeAlso => {(map,LatticePolarizedK3surface,ZZ,ZZ)}} 

document {Key => {(map,LatticePolarizedK3surface,ZZ,ZZ)}, 
Headline => "embedding of a K3 surface", 
Usage => "map S", 
Inputs => {"S" => LatticePolarizedK3surface,
           "a" => ZZ,
           "b" => ZZ}, 
Outputs => {{"the ",TO2{RationalMap,"birational morphism"}," defined by the complete linear system ",TEX///$|a H + b C|$///,", where ",TEX///$H,C$///," is the basis of the lattice associated to ",TEX///$S$///}}, 
EXAMPLE {"S = K3(3,1,-2)", "f = map(S,2,1);", "isMorphism f", "degree f", "image f == S(2,1)"}, 
SeeAlso => {(symbol SPACE,LatticePolarizedK3surface,Sequence)}} 

undocumented {(net,LatticePolarizedK3surface),(symbol ?,EmbeddedK3surface),(map,EmbeddedK3surface),(genus,EmbeddedK3surface)}

document {Key => {(vars,LatticePolarizedK3surface)}, 
Headline => "corresponding varieties", 
Usage => "vars S", 
Inputs => {"S" => LatticePolarizedK3surface => {"a lattice-polarized K3 surface with rank 2 lattice spanned by ",TEX///$H,C$///}}, 
Outputs => {EmbeddedProjectiveVariety => {"the special curve ",TEX///$C$///," contained in ",TEX///$S$///,", regarding ",TEX///$S$///," as embedded by ",TEX///$|H|$///},
            EmbeddedProjectiveVariety => {"the surface ",TEX///$S$///," embedded by ",TEX///$|H|$///}},
EXAMPLE {
"S = K3(5,2,-2)",
"first vars S",
"last vars S"},
SeeAlso => {(symbol SPACE,LatticePolarizedK3surface,Sequence)}} 

document {Key => {trigonalK3,(trigonalK3,ZZ),[trigonalK3,CoefficientRing]}, 
Headline => "trigonal K3 surface", 
Usage => "trigonalK3 g", 
Inputs => {"g" => ZZ =>{"the genus"}}, 
Outputs => {EmbeddedK3surface => {"a random trigonal K3 surface of genus ", TEX///$g$///," and degree ",TEX///$2g-2$///," in ",TEX///$\mathbb{P}^g$///}}, 
PARA{"This implements the construction given in the paper ",EM "A remark on the generalized franchetta conjecture for K3 surfaces",", by Beauville."},
EXAMPLE {"S = trigonalK3 11", "f = map S;", "image f", "U = source f", "multirationalMap first projections source f"}} 

document {Key => {mukaiModel,(mukaiModel,ZZ),[mukaiModel,CoefficientRing]}, 
Headline => "Mukai models", 
Usage => "mukaiModel g", 
Inputs => {"g" => ZZ =>{"the genus"}}, 
Outputs => {EmbeddedProjectiveVariety => {"the Mukai model of genus ",TEX///$g$///," and degree ",TEX///$2g-2$///}},
EXAMPLE {"X = mukaiModel 9;", "(degree X, sectionalGenus X)", "parametrize X"}} 

-- Tests --

TEST /// -- randomPointedMukaiThreefold
debug K3s;
K = ZZ/333331;
for g in {3,4,5,6,7,8,9,10,12} do (
    <<"g = "<<g<<endl;
    time (X,p) = randomPointedMukaiThreefold(g,CoefficientRing=>K);
    assert(coefficientRing ring X === K and dim ambient X == g+1);
    assert isSubset(p,X);
    assert (? ideal p == "one-point scheme in PP^"|toString(g+1));
    assert(dim X == 3);
    assert(sectionalGenus X == g);
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
    assert(coefficientRing ring X === K and dim ambient X == g+1);
    assert isSubset(L,X);
    assert (? ideal L == "line in PP^"|toString(g+1));
    assert(dim X == 3);
    assert(sectionalGenus X == g);
    assert(degree X == 2*g-2);
);
///

TEST ///
for g from 3 to 12 do (
    <<"(g,d,n) = "<<(g,2,-2)<<endl;
    time S = K3(g,2,-2);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 1 and degree C == 2 and sectionalGenus C == 0 and isSubset(C,T));
    assert(L == matrix{{2*g-2,2},{2,-2}});
);
///

TEST ///
for g in {3,4,5,6,7,8,9} do (
    <<"(g,d,n) = "<<(g,1,-2)<<endl;
    time S = K3(g,1,-2);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 1 and degree C == 1 and sectionalGenus C == 0 and isSubset(C,T));
    assert(L == matrix{{2*g-2,1},{1,-2}}); 
);
///

TEST ///
setRandomSeed 123456789;
for g in {10,12} do (
    <<"(g,d,n) = "<<(g,1,-2)<<endl;
    time S = K3(g,1,-2);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 1 and degree C == 1 and sectionalGenus C == 0 and isSubset(C,T));
    assert(L == matrix{{2*g-2,1},{1,-2}}); 
);
///

TEST ///
for e in 
select({3,4,5} ** toList(3..8),e -> ((g,d) = toSequence e; (member(g,{3,4,5}) and d >= 3) and (g != 5 or d <= 8) and (g != 4 or d <= 6) and (g != 3 or d <= 8)))
do (
    (g,d) := toSequence e;
    <<"(g,d,n) = "<<(g,d,-2)<<endl;
    time S = K3(g,d,-2);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 1 and degree C == d and sectionalGenus C == 0 and isSubset(C,T));
    assert(L == matrix{{2*g-2,d},{d,-2}});   
);
///

TEST ///
for e in 
select({3,4,5} ** toList(3..9),e -> ((g,d) = toSequence e; (member(g,{3,4,5}) and member(d,{3,4,5,6,7,8,9})) and (g != 5 or d <= 9) and (g != 4 or d <= 7) and (g != 3 or d <= 8)))
do (
    (g,d) := toSequence e;
    <<"(g,d,n) = "<<(g,d,0)<<endl;
    time S = K3(g,d,0);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 1 and degree C == d and sectionalGenus C == 1 and isSubset(C,T));
    assert(L == matrix{{2*g-2,d},{d,0}});    
);
///

TEST ///
for g in {3,4,5,6,7,8,9,10,12} do (
    <<"(g,d,n) = "<<(g,0,-2)<<endl;
    time S = K3(g,0,-2);
    T = S#"surface";
    C = S#"curve";
    L = S#"lattice";
    assert(dim T == 2 and degree T == 2*g-2 and sectionalGenus T == g and dim ambient T == g);
    assert(dim C == 0 and degree C == 1 and isSubset(C,T) and dim tangentSpace(T,C) > 2);
    assert(L == matrix{{2*g-2,0},{0,-2}});       
);
///

TEST ///
for g in {3,4,5,6,7,8,9,10,12} do (<<"g = "<<g<<endl; time K3 g); 
///;

TEST ///
K3 11 
///

end;

TEST ///
K3 20
///

TEST ///
K3 22
///

-*
i2 : check K3s -- (Sun 19 Sep 19:38:19 CEST 2021)
 -- capturing check(0, "K3s")                                                -- 153.544 seconds elapsed
 -- capturing check(1, "K3s")                                                -- 158.334 seconds elapsed
 -- capturing check(2, "K3s")                                                -- 507.99 seconds elapsed
 -- capturing check(3, "K3s")                                                -- 8.08465 seconds elapsed
 -- capturing check(4, "K3s")                                                -- 180.602 seconds elapsed
 -- capturing check(5, "K3s")                                                -- 6.05575 seconds elapsed
 -- capturing check(6, "K3s")                                                -- 11.866 seconds elapsed
 -- capturing check(7, "K3s")                                                -- 186.685 seconds elapsed
 -- capturing check(8, "K3s")                                                -- 190.407 seconds elapsed
 -- capturing check(9, "K3s")                                                -- 384.407 seconds elapsed
*-


